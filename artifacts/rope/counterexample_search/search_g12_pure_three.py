"""Target the certified four-vanilla-head twelve-bit function with three pure heads.

Numerical failure is inconclusive. Any successful fit is rationalized and checked
on every input by exact arithmetic before being called a certificate.
Run numerical work through ``heavy python3 ...``.
"""
import argparse
import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize


def data(target='g12'):
    n=12 if target=='g12' else 8
    z=np.array([[2*((m>>i)&1)-1 for i in range(n)] for m in range(1<<n)],float)
    if target=='g12':
        q=22+20*np.sum(z[:,::2]*z[:,1::2],axis=1)-np.sum(z,axis=1)**2
    else:
        q=z[:,7]*np.sum(z[:,4:7]*(2*z[:,:3]-z[:,3,None]),axis=1)
    assert np.all(q)
    return z,np.sign(q)


def unpack(theta,n,h):
    r=theta[:h*(n+1)].reshape(h,n+1)
    r=r-r.max(axis=1,keepdims=True)
    mass=np.exp(r); mass/=mass.sum(axis=1,keepdims=True)
    s=mass[:,:n]
    t=np.tanh(theta[h*(n+1):h*(2*n+1)].reshape(h,n))
    b=s*t
    coeff=theta[h*(2*n+1):]
    return mass,s,t,b,coeff


def loss_gradient(theta,z,y,h,reg=1e-10):
    n=z.shape[1]
    mass,s,t,b,co=unpack(theta,n,h)
    k=co[1:1+h]; l=co[1+h:]
    u=z@s.T; bb=z@b.T; d=1+bb
    num=u*k+bb*l
    score=co[0]+np.sum(num/d,axis=1)
    gap=np.minimum(y*score-1,0)
    loss=np.mean(gap**2)+reg*np.sum(co*co)
    gp=2*gap*y/len(y)
    gu=(gp[:,None]*k/d).T@z
    gb=(gp[:,None]*(l-k*u)/(d*d)).T@z
    gs=gu+gb*t
    gm=np.column_stack([gs,np.zeros(h)])
    gr=mass*(gm-np.sum(gm*mass,axis=1,keepdims=True))
    gt=gb*s*(1-t*t)
    gc=np.concatenate([[np.sum(gp)],np.sum(gp[:,None]*u/d,axis=0),np.sum(gp[:,None]*bb/d,axis=0)])+2*reg*co
    grad=np.concatenate([gr.ravel(),gt.ravel(),gc])
    return loss,grad


def cleared_loss_gradient(theta,z,y,h,alpha=1.,reg=1e-12):
    """Even quadratic plus alpha times the odd part of the cleared cubic."""
    assert h==3
    n=z.shape[1]
    mass,s,t,b,co=unpack(theta,n,h)
    k=co[1:1+h]; l=co[1+h:]
    u=z@s.T; bb=z@b.T
    num=u*k+bb*l
    fs=np.column_stack([bb[:,1]+bb[:,2],bb[:,0]+bb[:,2],bb[:,0]+bb[:,1]])
    fp=np.column_stack([bb[:,1]*bb[:,2],bb[:,0]*bb[:,2],bb[:,0]*bb[:,1]])
    ft=1+np.sum(fp,axis=1)+alpha*(np.sum(bb,axis=1)+np.prod(bb,axis=1))
    fh=fs+alpha*(1+fp)
    score=co[0]*ft+np.sum(num*fh,axis=1)
    gap=np.minimum(y*score-1,0)
    loss=np.mean(gap**2)+reg*np.sum(co*co)
    gp=2*gap*y/len(y)
    gu=(gp[:,None]*k*fh).T@z
    gb0=co[0]*(fs+alpha*(1+fp))+l*fh
    for j in range(3):
        for r in range(3):
            if r!=j:
                other=3-j-r
                gb0[:,j]+=num[:,r]*(1+alpha*bb[:,other])
    gb=(gp[:,None]*gb0).T@z
    gs=gu+gb*t
    gm=np.column_stack([gs,np.zeros(h)])
    gr=mass*(gm-np.sum(gm*mass,axis=1,keepdims=True))
    gt=gb*s*(1-t*t)
    gc=np.concatenate([[np.sum(gp*ft)],np.sum(gp[:,None]*u*fh,axis=0),np.sum(gp[:,None]*bb*fh,axis=0)])+2*reg*co
    return loss,np.concatenate([gr.ravel(),gt.ravel(),gc])


def linear_refit(theta,z,y,h):
    n=z.shape[1]
    mass,s,t,b,co=unpack(theta,n,h)
    u=z@s.T; bb=z@b.T; d=1+bb
    features=np.column_stack([np.ones(len(y)),u/d,bb/d])
    lp=linprog(np.zeros(1+2*h),A_ub=-y[:,None]*features,b_ub=-np.ones(len(y)),bounds=[(None,None)]*(1+2*h),method='highs')
    if lp.success:
        theta[-(1+2*h):]=lp.x
    score=features@theta[-(1+2*h):]
    return lp.success,float(np.min(y*score)),int(np.sum(y*score<=0))


def init(rng,n,h,mode):
    r=rng.normal(0,1,(h,n+1))
    t=rng.normal(0,1,(h,n))
    if mode%3==0:
        r[:,:n]=-3
        for j in range(h):
            r[j,4*j:4*j+4]=0
            t[j,4*j:4*j+2]=2
            t[j,4*j+2:4*j+4]=-2
        r[:,-1]=-2
        r+=rng.normal(0,.1,r.shape)
    elif mode%3==1:
        r[:,:n]=rng.normal(0,.3,(h,n))
        r[:,-1]=-3
        t=3*np.sign(rng.normal(size=(h,n)))+rng.normal(0,.1,(h,n))
    co=rng.normal(0,20,1+2*h)
    return np.concatenate([r.ravel(),t.ravel(),co])


def parity_init(rng,n,j):
    """Start from an exact three-head parity classifier on a selected triple."""
    coords=[j%3,4+j%3,7]
    if j%6>=3:
        coords[0]=3
    betas=np.array([.1,.2,.3])
    s=np.full((3,n),.001)
    b=np.zeros((3,n))
    for h in range(3):
        s[h,coords]=betas[h]+.01
        b[h,coords]=betas[h]
    gamma=1-s.sum(axis=1)
    r=np.log(np.column_stack([s,gamma]))
    t=np.arctanh(b/s)
    mat=np.stack([betas,betas*(betas.sum()-betas),np.full(3,np.prod(betas))])
    ell=np.linalg.solve(mat,np.array([-4.,0.,1.]))
    ell*=1 if j%6<3 else -1
    co=np.concatenate([[0.],np.zeros(3),ell])
    theta=np.concatenate([r.ravel(),t.ravel(),co])
    theta+=rng.normal(0,.001,theta.shape)
    return theta


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--restarts',type=int,default=30)
    ap.add_argument('--maxiter',type=int,default=3000)
    ap.add_argument('--seed',type=int,default=223344)
    ap.add_argument('--out',default='/tmp/g12_pure_three_search.jsonl')
    ap.add_argument('--resume')
    ap.add_argument('--continuation',action='store_true')
    ap.add_argument('--target',choices=['g12','f7xor'],default='g12')
    ap.add_argument('--parity-init',action='store_true')
    args=ap.parse_args()
    z,y=data(args.target); h=3; n=z.shape[1]; rng=np.random.default_rng(args.seed)
    base=None
    if args.resume:
        records=[json.loads(l) for l in Path(args.resume).read_text().splitlines()]
        base=np.array(min(records,key=lambda r:r['loss'])['theta'])
    for j in range(args.restarts):
        start=time.time()
        theta=(parity_init(rng,n,j) if args.parity_init else init(rng,n,h,j)) if base is None else base+rng.normal(0,.05+0.05*(j%4),base.shape)
        if args.continuation:
            stages=[]
            for alpha in [0.,.01,.05,.2,1.]:
                res=minimize(cleared_loss_gradient,theta,args=(z,y,h,alpha),jac=True,method='L-BFGS-B',options={'maxiter':args.maxiter,'ftol':1e-14,'gtol':1e-8,'maxls':40})
                theta=res.x
                stages.append([alpha,float(res.fun),res.nit])
                print('stage',j,stages[-1],flush=True)
        else:
            stages=[]
            res=minimize(loss_gradient,theta,args=(z,y,h),jac=True,method='L-BFGS-B',options={'maxiter':args.maxiter,'ftol':1e-14,'gtol':1e-8,'maxls':40})
            theta=res.x
        success,margin,errors=linear_refit(theta,z,y,h)
        record={'restart':j,'seed':args.seed,'loss':float(res.fun),'margin':margin,'errors':errors,'success':success,'iterations':res.nit,'stages':stages,'seconds':time.time()-start,'theta':theta.tolist()}
        with Path(args.out).open('a') as f:
            f.write(json.dumps(record)+'\n')
        print({k:v for k,v in record.items() if k!='theta'},flush=True)
        if success:
            print('FLOATING FEASIBILITY FOUND. EXACT CERTIFICATE STILL REQUIRED.',flush=True)
            break


if __name__=='__main__':
    main()
