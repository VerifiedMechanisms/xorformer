#!/usr/bin/env python3
"""Explore jointly chosen row directions on independently labeled cube columns.

Run under heavy. For every target family the directions, shared affine row
numerators, column residues, offsets and biases may be selected afresh.
Offsets stay in [1,1+delta]. Positivity is exact on the row cube because all
row slopes and offsets are positive. These are auxiliary row decoders; the
full reverse one-star transfer must separately charge its axis repair.

A floating LP success is rechecked with exact Fraction arithmetic after
rounding all input parameters and coefficients. Optimizer failure proves
nothing. Each successful certificate concerns only the displayed finite
label family, not every family or an asymptotic bound.
"""
import argparse, itertools, json, time
from fractions import Fraction
import numpy as np
from scipy.optimize import minimize, linprog
import torch


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--dimension',type=int,default=4)
    p.add_argument('--heads',type=int,default=4)
    p.add_argument('--columns',type=int,default=4)
    p.add_argument('--targets',type=int,default=10)
    p.add_argument('--restarts',type=int,default=10)
    p.add_argument('--iterations',type=int,default=200)
    p.add_argument('--delta',type=float,default=.05)
    p.add_argument('--seed',type=int,default=241124)
    p.add_argument('--affine-row',action='store_true')
    p.add_argument('--paired',action='store_true',help='Subtract each shared row numerator at the common baseline offset.')
    p.add_argument('--baseline',type=float,default=1.)
    p.add_argument('--sign-cone',action='store_true',help='Optimize positive target magnitudes as well as directions.')
    p.add_argument('--output')
    args=p.parse_args()
    torch.set_num_threads(1)
    torch.set_default_dtype(torch.float64)
    rng=np.random.default_rng(args.seed)
    k,H,s=args.dimension,args.heads,args.columns
    bits=np.array(list(itertools.product((0,1),repeat=k)),dtype=float)
    N=len(bits); M=N*s
    xb=torch.tensor(bits)
    cj=torch.eye(s)
    start=time.monotonic()

    def features(theta):
        d=.01+torch.nn.functional.softplus(theta[:H*k].reshape(H,k))
        b=1+args.delta*torch.sigmoid(theta[H*k:H*(k+s)].reshape(H,s))
        r=1/(xb@d.T)[:,:,None].add(b[None,:,:])
        # Row order is (cube vertex, column), coefficient blocks are
        # column biases, head/column residues, head/row shared slopes.
        z0=cj[None,:,:].expand(N,-1,-1).reshape(M,s)
        z1=(r[:,:,:,None]*cj[None,None,:,:]).permute(0,2,1,3).reshape(M,H*s)
        parts=[z0,z1]
        if args.affine_row:
            row_r=r
            if args.paired:
                baseline=1/((xb@d.T)+args.baseline)
                row_r=r-baseline[:,:,None]
            z2=(row_r[:,:,:,None]*xb[:,None,None,:]).permute(0,2,1,3).reshape(M,H*k)
            parts.append(z2)
        return torch.cat(parts,dim=1),d,b

    def solve_lp(z,y):
        # Scaling columns makes the numerical LP better conditioned.
        norms=np.linalg.norm(z,axis=0)
        norms=np.maximum(norms,1e-100)
        zr=z/norms
        out=linprog(np.zeros(z.shape[1]),A_ub=-y[:,None]*zr,
            b_ub=-np.ones(M),bounds=[(None,None)]*z.shape[1],method='highs')
        if not out.success:return None
        c=out.x/norms
        if np.min(y*(z@c))<=.01:return None
        return c

    def certificate(d,b,c,y):
        # Decimal-rounding every value makes this check independent of the
        # floating objective, LP feasibility tolerances and BLAS backend.
        frac=lambda x:Fraction(format(float(x),'.16g'))
        dd=[[frac(x) for x in row] for row in d]
        bb=[[frac(x) for x in row] for row in b]
        cc=[frac(x) for x in c]
        delta=frac(args.delta)
        if not all(x>0 for row in dd for x in row):return None
        if not all(1<=x<=1+delta for row in bb for x in row):return None
        baseline=frac(args.baseline)
        embedding=max(1+delta,baseline)+delta
        if args.paired:
            if not s*(embedding-baseline)<embedding:return None
            if not all(sum(embedding-x for x in row)<embedding for row in bb):return None
        margin=None
        for ix,x in enumerate(bits.astype(int)):
            for j in range(s):
                val=cc[j]
                for h in range(H):
                    num=cc[s+h*s+j]
                    if args.affine_row:
                        num+=sum(cc[s+H*s+h*k+i]*int(x[i]) for i in range(k))
                    den=bb[h][j]+sum(dd[h][i]*int(x[i]) for i in range(k))
                    val+=num/den
                    if args.paired and args.affine_row:
                        rownum=sum(cc[s+H*s+h*k+i]*int(x[i]) for i in range(k))
                        val-=rownum/(baseline+sum(dd[h][i]*int(x[i]) for i in range(k)))
                m=int(y[ix*s+j])*val
                if m<=0:return None
                margin=m if margin is None else min(margin,m)
        return {'baseline':str(baseline),'embedding_intercept':str(embedding),'directions':[[str(x) for x in row] for row in dd],
            'offsets':[[str(x) for x in row] for row in bb],
            'coefficients':[str(x) for x in cc],
            'exact_min_margin':str(margin)}

    records=[]
    for target in range(args.targets):
        y=rng.choice([-1.,1.],size=M)
        # Include hard parity columns in the first family.
        if target==0:
            for j in range(s):
                mask=np.array([(j+1)>>i&1 for i in range(k)])
                if j==s-1:mask=np.ones(k,dtype=int)
                y[j::s]=1-2*((bits@mask).astype(int)%2)
        yt=torch.tensor(y)
        best=1e100;cert=None;used=0;evals=0
        for restart in range(args.restarts):
            used=restart+1
            theta=rng.normal(size=H*(k+s))
            if args.sign_cone:theta=np.r_[theta,np.zeros(M)]
            def fun(a):
                nonlocal evals
                t=torch.tensor(a,requires_grad=True)
                z,_,_=features(t)
                # Full SVD pseudoinverse; no ridge restriction on coefficients.
                target_y=yt
                if args.sign_cone:
                    target_y=yt*(1+torch.nn.functional.softplus(t[H*(k+s):]))
                c=torch.linalg.pinv(z,rtol=1e-12)@target_y
                residual=z@c-target_y
                loss=torch.mean(residual**2)
                loss.backward()
                evals+=1
                return float(loss.detach()),t.grad.detach().numpy()
            out=minimize(fun,theta,jac=True,method='L-BFGS-B',
                options={'maxiter':args.iterations,'ftol':1e-13,'gtol':1e-8,'maxls':30})
            best=min(best,float(out.fun))
            with torch.no_grad():
                z,d,b=features(torch.tensor(out.x))
            zn=z.numpy();c=solve_lp(zn,y)
            if c is not None:
                cert=certificate(d.numpy(),b.numpy(),c,y)
                if cert is not None:break
        rec={'target':target,'labels':y.astype(int).reshape(N,s).tolist(),
            'best_mean_square_error':best,'restarts':used,'evaluations':evals,
            'seconds':time.monotonic()-start,'certificate':cert}
        records.append(rec)
        print(json.dumps({key:value for key,value in rec.items() if key not in ['labels','certificate']}
            |{'exact_certificate':cert is not None}),flush=True)
        if args.output:
            with open(args.output,'w') as f:json.dump({'args':vars(args),'records':records},f)
    print(json.dumps({'certified':sum(r['certificate'] is not None for r in records),
        'total':len(records),'seconds':time.monotonic()-start}),flush=True)

if __name__=='__main__':main()
