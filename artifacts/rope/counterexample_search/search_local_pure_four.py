"""Fit four pure heads to a finite vanilla-four obstruction pattern.

Only successful exact verification can certify a separation. Optimizer failure
has no lower-bound meaning. Selector is coordinate 16; X_i=2i, Y_i=2i+1.
Run numerical fitting through ``heavy python3 ...``.
"""
import argparse
import json
import time
from pathlib import Path
from fractions import Fraction

import numpy as np
from scipy.optimize import minimize

from search_g12_pure_three import init, linear_refit, loss_gradient, unpack


def data(pattern='old'):
    base=np.full(16,-1.0)
    points=[(base,-1.)]
    for i in range(16):
        z=base.copy(); z[i]=1
        points.append((z,1.))
    for i in range(8):
        for j in range(8):
            if i!=j:
                z=base.copy(); z[2*i]=z[2*j+1]=1
                points.append((z,-1.))
    if pattern=='old':
        for j in range(8):
            for k in range(j+1,8):
                z=base.copy(); z[2*j+1]=z[2*k+1]=1
                points.append((z,-1.))
    else:
        for j in range(8):
            plus={1,2,3} if j==0 else {0,*[k for k in range(1,8) if k!=j][:2]}
            v=np.array([1 if k in plus else -1 for k in range(8)])
            for orientation in [-1,1]:
                for value in [-1,1]:
                    z=base.copy();z[1::2]=orientation*v;z[2*j+1]=value
                    points.append((z,float(-value)))
    zs=[]; ys=[]
    for z,y in points:
        for orientation in [-1,1]:
            for t in [-1,1]:
                zs.append(np.append(orientation*z,t)); ys.append(t*y)
    assert len(zs)==(404 if pattern=='old' else 420)
    # Repeated witnesses are harmless, but their labels must agree exactly.
    labels={}
    for z,y in zip(zs,ys):
        key=tuple(z)
        assert key not in labels or labels[key]==y
        labels[key]=y
    return np.array(zs),np.array(ys)


def project(values):
    """Orthogonal projection onto selector-odd, spatial-complement-even values."""
    signs=np.array([-1,1,-1,1.])
    vals=values.reshape(-1,4)
    return (np.mean(vals*signs,axis=1)[:,None]*signs).ravel()


def cleared_loss_gradient(theta,z,y,h=4,alpha=1.,reg=1e-24):
    n=z.shape[1]
    mass,s,t,b,co=unpack(theta,n,h)
    k=co[1:1+h]; ell=co[1+h:]
    u=z@s.T; bb=z@b.T; den=1+bb
    num=u*k+bb*ell
    allprod=np.prod(den,axis=1)
    excl=np.column_stack([np.prod(den[:,[r for r in range(h) if r!=j]],axis=1) for j in range(h)])
    score=co[0]*allprod+np.sum(num*excl,axis=1)
    score=alpha*score+(1-alpha)*project(score)
    gap=np.minimum(y*score-1,0)
    gp=2*gap*y/len(y)
    gp=alpha*gp+(1-alpha)*project(gp)
    loss=np.mean(gap**2)+reg*np.sum(co*co)
    gu=(gp[:,None]*k*excl).T@z
    gb0=co[0]*excl+ell*excl
    for j in range(h):
        for r in range(h):
            if j!=r:
                gb0[:,j]+=num[:,r]*np.prod(den[:,[a for a in range(h) if a not in [r,j]]],axis=1)
    gb=(gp[:,None]*gb0).T@z
    gs=gu+gb*t
    gm=np.column_stack([gs,np.zeros(h)])
    gr=mass*(gm-np.sum(gm*mass,axis=1,keepdims=True))
    gt=gb*s*(1-t*t)
    gc=np.concatenate([[np.sum(gp*allprod)],np.sum(gp[:,None]*u*excl,axis=0),np.sum(gp[:,None]*bb*excl,axis=0)])+2*reg*co
    return loss,np.concatenate([gr.ravel(),gt.ravel(),gc])


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--restarts',type=int,default=24)
    ap.add_argument('--maxiter',type=int,default=5000)
    ap.add_argument('--seed',type=int,default=404174)
    ap.add_argument('--out',default='/tmp/local_pure_four.jsonl')
    ap.add_argument('--resume')
    ap.add_argument('--algebra-seed')
    ap.add_argument('--direct',action='store_true')
    ap.add_argument('--continuation',action='store_true')
    ap.add_argument('--pattern',choices=['old','middle'],default='old')
    ap.add_argument('--projected-only',action='store_true')
    args=ap.parse_args()
    z,y=data(args.pattern); n=17; h=4; rng=np.random.default_rng(args.seed)
    base=None
    if args.resume:
        records=[json.loads(l) for l in Path(args.resume).read_text().splitlines()]
        base=np.array(min(records,key=lambda r:r['loss'])['theta'])
    if args.algebra_seed:
        seed=json.loads(Path(args.algebra_seed).read_text())
        order=[i for j in range(8) for i in [j+1,j+9]]+[0]
        s=np.array([[float(Fraction(x)) for x in row] for row in seed['S']])[order].T
        b=np.array([[float(Fraction(x)) for x in row] for row in seed['B']])[order].T
        co=np.array([float(Fraction(seed['T']))]+[float(Fraction(x)) for x in seed['k'][0]+seed['ell'][0]])
        base=np.concatenate([np.log(np.column_stack([s,1-s.sum(axis=1)])).ravel(),np.arctanh(b/s).ravel(),co])
    for j in range(args.restarts):
        start=time.time()
        theta=init(rng,n,h,j) if base is None else base+rng.normal(0,0 if j==0 else .01+.03*(j%4),base.shape)
        theta[:h*(2*n+1)]=np.clip(theta[:h*(2*n+1)],-10,10)
        stages=[]
        projected_theta=None
        for alpha in ([0.] if args.projected_only else [0.,.001,.01,.05,.2,1.] if args.continuation else [1.]):
            lossfn=loss_gradient if args.direct else cleared_loss_gradient
            fnargs=(z,y,h) if args.direct else (z,y,h,alpha)
            res=minimize(lossfn,theta,args=fnargs,jac=True,method='L-BFGS-B',bounds=[(-10,10)]*(h*(2*n+1))+[(None,None)]*(1+2*h),options={'maxiter':args.maxiter,'ftol':1e-14,'gtol':1e-9,'maxls':40})
            theta=res.x
            if alpha==0:projected_theta=theta.tolist()
            stages.append([alpha,float(res.fun),res.nit])
            if args.continuation:
                print('stage',j,stages[-1],flush=True)
        success,margin,errors=linear_refit(theta,z,y,h)
        record={'restart':j,'seed':args.seed,'pattern':args.pattern,'loss':float(res.fun),'margin':margin,'errors':errors,'success':success,'iterations':res.nit,'stages':stages,'seconds':time.time()-start,'theta':theta.tolist()}
        if projected_theta is not None:record['projected_theta']=projected_theta
        with Path(args.out).open('a') as f:
            f.write(json.dumps(record)+'\n')
        print({k:v for k,v in record.items() if k not in ['theta','projected_theta']},flush=True)
        if success:
            print('FLOATING FEASIBILITY FOUND. EXACT CERTIFICATE REQUIRED.',flush=True)
            break


if __name__=='__main__':
    main()
