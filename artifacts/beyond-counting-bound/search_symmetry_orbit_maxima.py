#!/usr/bin/env python3
"""Numerical diagnostic only: symmetric-target positive-head local minima."""
import argparse, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
def data(n,a,b):
    k=GROUP_SIZE
    codes=np.arange(2**n)
    X=((codes[:,None] >> np.arange(n)) & 1).astype(float)
    Y=np.concatenate([np.ones((len(X),1)),X],axis=1)
    D=1+X@b
    T=(Y@a)/D
    V=Y/D[:,None]
    Vb=X/D[:,None]
    J=np.concatenate([V,-T[:,None]*Vb],axis=1)
    dd=np.zeros((len(X),2*n+1,2*n+1))
    for x in range(len(X)):
        cross=np.outer(V[x],Vb[x])
        dd[x,:n+1,n+1:]=-cross
        dd[x,n+1:,:n+1]=-cross.T
        dd[x,n+1:,n+1:]=2*T[x]*np.outer(Vb[x],Vb[x])
    mask=(1<<k)-1
    orbit_keys=[(int(code)&mask).bit_count()+(k+1)*(int(code)>>k) for code in codes]
    keys=sorted(set(orbit_keys))
    O=np.array([[int(k==key) for key in keys] for k in orbit_keys],float)
    return X,T,J,dd,O,keys




def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--seconds',type=float,default=1800)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--group',type=int,default=3)
    args=ap.parse_args()
    global GROUP_SIZE
    GROUP_SIZE=args.group
    rng=np.random.default_rng(202611231735)
    start=time.monotonic();trial=0;counts={}
    with args.output.open('w') as out:
        while time.monotonic()-start<args.seconds:
            n=args.group+2+trial%3
            X,T,J,dd,O,keys=data(n,np.ones(n+1),np.ones(n))
            Y=np.column_stack([np.ones(len(X)),X])
            scale=10.0**(trial%5-2)
            if (trial//5)%2:
                z=rng.normal(size=len(keys))*scale
            else:
                z=np.exp(rng.normal(size=len(keys))*min(scale,3))
            # The family contains constants. Remove the target mean before
            # normalizing, so near-constant targets do not mask residuals.
            z=z-np.mean(O@z)
            mu=O@z
            mu/=np.linalg.norm(mu)
            def obj(logb,ret=False):
                b=np.exp(logb);D=1+X@b
                Z=Y/D[:,None]
                a=np.linalg.lstsq(Z,mu,rcond=1e-12)[0]
                t=Z@a;r=t-mu
                g=-2*b*(X.T@(r*t/D))
                return (a,b,t,r,g) if ret else (r@r,g)
            init=rng.uniform(-2,3,n)
            sol=minimize(obj,init,jac=True,method='L-BFGS-B',bounds=[(-9,9)]*n,
                options={'maxiter':600,'ftol':1e-15,'gtol':1e-10,'maxls':40})
            a,b,t,r,g=obj(sol.x,True)
            status='boundary' if np.max(abs(sol.x))>8.95 else 'interior'
            if status=='interior' and np.max(abs(g))<1e-7:
                _,_,j,dds,_,_=data(n,a,b)
                u,s,vh=np.linalg.svd(j,full_matrices=False)
                if s[-1]>1e-8*s[0]:
                    Z=vh.T/s[None,:]
                    # Enforce stationarity in orthonormal tangent coordinates.
                    # A small raw parameter gradient is not sufficient when J
                    # is ill-conditioned near a constant head table.
                    eq=u.T@O;rhs=u.T@t
                    zfix=z/np.linalg.norm(O@z)
                    zfix+=np.linalg.lstsq(eq,rhs-eq@zfix,rcond=1e-12)[0]
                    r=t-O@zfix
                    tangent_residual=np.max(abs(u.T@r))
                    h=np.eye(2*n+1)+np.einsum('x,ia,xij,jb->ab',r,Z,dds,Z)
                    eig=np.linalg.eigvalsh(h)
                    sep=min(abs(b[i]-b[j])/(1+b[i]+b[j]) for i in range(args.group) for j in range(i))
                    if eig[0]>.01 and sep>1e-3 and tangent_residual<1e-9:
                        rec=dict(trial=trial,n=n,a=a.tolist(),b=b.tolist(),orbit_keys=keys,
                            orbit_mu=zfix.tolist(),minimum_eigenvalue=float(eig[0]),
                            gradient=float(np.max(abs(g))),separation=float(sep),group_size=args.group,
                            tangent_stationarity_residual=float(tangent_residual),
                            status='NUMERICAL CANDIDATE ONLY',main_target_proved=False,
                            elapsed=time.monotonic()-start)
                        out.write(json.dumps(rec)+'\n');out.flush()
                        print(json.dumps(rec),flush=True)
                        break
                    status='interior_not_certifiable'
                else:status='rank'
            counts[status]=counts.get(status,0)+1
            if trial%20==0:
                print(json.dumps(dict(trial=trial,elapsed=time.monotonic()-start,counts=counts)),flush=True)
            trial+=1


if __name__=='__main__':main()
