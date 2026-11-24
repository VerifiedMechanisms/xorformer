"""Target mixed-literal three-term tribes, with an explicit pure-three upper bound.

Fitting failure is inconclusive. Successful vanilla fits must be rationalized
and checked exactly before they are certificates.
"""
import argparse
import json
import time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog,minimize


def data(size):
    n=3*size
    x=np.array([[(m>>i)&1 for i in range(n)] for m in range(1<<n)],float)
    pattern=np.array([1]*(size//2)+[0]*(size-size//2))
    y=np.where(np.any(np.all(x.reshape(-1,3,size)==pattern[None,None,:],axis=2),axis=1),1.,-1.)
    return 2*x-1,y


def fit(z,y,restarts,seed,maxiter,initial=None,regularization=1e-12):
    n=z.shape[1];h=3;rng=np.random.default_rng(seed)
    x=np.column_stack([np.ones(len(z)),z])
    for restart in range(restarts):
        orientations=np.array([1. if j>=restart%4 else -1. for j in range(h)]) if initial is None else np.sign(np.array(initial['beta'])[:,0])
        def fg(theta):
            logits=theta[:h*(n+1)].reshape(h,n+1)
            logits=logits-logits.max(axis=1,keepdims=True)
            mass=np.exp(logits);mass/=mass.sum(axis=1,keepdims=True)
            beta=orientations[:,None]*mass[:,1:]
            d=1+z@beta.T
            a=theta[h*(n+1):].reshape(h,n+1)
            num=x@a.T
            pairs=np.column_stack([d[:,1]*d[:,2],d[:,0]*d[:,2],d[:,0]*d[:,1]])
            p=np.sum(num*pairs,axis=1)
            gap=np.minimum(y*p-1,0)
            reg=regularization
            loss=np.mean(gap*gap)+reg*np.sum(a*a)
            gp=2*gap*y/len(y)
            ga=(gp[:,None]*pairs).T@x+2*reg*a
            gd=np.zeros_like(d)
            for j in range(3):
                for r in range(3):
                    if j!=r:
                        gd[:,j]+=num[:,r]*d[:,3-j-r]
            gb=(gp[:,None]*gd).T@z
            gm=np.column_stack([np.zeros(h),orientations[:,None]*gb])
            gl=mass*(gm-np.sum(gm*mass,axis=1,keepdims=True))
            return loss,np.r_[gl.ravel(),ga.ravel()]
        if initial is None:
            theta=rng.normal(0,1,2*h*(n+1))
            theta[:h*(n+1)]*=2
        else:
            b=np.abs(np.array(initial['beta']))
            weights=np.column_stack([np.maximum(1e-12,1-b.sum(axis=1)),b])
            theta=np.r_[np.log(np.maximum(weights,1e-12)).ravel(),np.array(initial['numerators']).ravel()]
            if restart:
                theta[:h*(n+1)]+=rng.normal(0,.1+.2*restart,h*(n+1))
        start=time.time()
        res=minimize(fg,theta,jac=True,method='L-BFGS-B',options={'maxiter':maxiter,'ftol':1e-14,'gtol':1e-9,'maxls':40})
        logits=res.x[:h*(n+1)].reshape(h,n+1)
        mass=np.exp(logits-logits.max(axis=1,keepdims=True));mass/=mass.sum(axis=1,keepdims=True)
        beta=orientations[:,None]*mass[:,1:]
        den=1+z@beta.T
        features=np.column_stack([x*den[:,1,None]*den[:,2,None],x*den[:,0,None]*den[:,2,None],x*den[:,0,None]*den[:,1,None]])
        lp=linprog(np.zeros(h*(n+1)),A_ub=-y[:,None]*features,b_ub=-np.ones(len(y)),bounds=[(None,None)]*(h*(n+1)),method='highs')
        record={'restart':restart,'seed':seed,'loss':float(res.fun),'success':lp.success,'seconds':time.time()-start,'beta':beta.tolist(),'numerators':lp.x.reshape(h,n+1).tolist() if lp.success else None,'optimizer_numerators':res.x[h*(n+1):].reshape(h,n+1).tolist()}
        yield record
        if lp.success:
            return


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--size',type=int,default=3)
    ap.add_argument('--restarts',type=int,default=20)
    ap.add_argument('--maxiter',type=int,default=10000)
    ap.add_argument('--seed',type=int,default=606060)
    ap.add_argument('--out',default='/tmp/mixed_tribes_vanilla.jsonl')
    args=ap.parse_args();z,y=data(args.size)
    for record in fit(z,y,args.restarts,args.seed,args.maxiter):
        record['size']=args.size
        with Path(args.out).open('a') as f:f.write(json.dumps(record)+'\n')
        print({k:v for k,v in record.items() if k not in ['beta','numerators']},flush=True)


if __name__=='__main__':
    main()
