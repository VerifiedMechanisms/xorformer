#!/usr/bin/env python3
"""Floating exploratory projection optimization, not a proof or certificate."""
import argparse, itertools, json, time
import numpy as np
from scipy.optimize import minimize
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=4);p.add_argument('--heads',type=int,default=2);p.add_argument('--starts',type=int,default=100);p.add_argument('--seconds',type=float,default=240);p.add_argument('--out',required=True);a=p.parse_args()
n=a.n;H=a.heads
X=np.array(list(itertools.product([0.,1.],repeat=n)));N=len(X)
ix=np.all(X==np.array([1.]*(n//2)+[0.]*(n-n//2)),axis=1).nonzero()[0][0]
y=np.zeros(N);y[ix]=1
rng=np.random.default_rng(1357+n+H);started=time.monotonic();records=[]
# Gauge fixes one log weight in each head at0. Each orientation has strictlypositive
# intercept and nonzero coherent slopes, so these are genuine admissible ratios.
for pos in range(H+1):
    orientations=[1]*pos+[-1]*(H-pos)
    Z=[np.column_stack([np.ones(N),X if o==1 else 1-X]) for o in orientations]
    best=None
    def calc(theta,gradient=True):
        W=np.exp(np.column_stack([np.zeros(H),theta.reshape(H,n)]))
        D=np.array([z@w for z,w in zip(Z,W)])
        F=np.column_stack([np.ones(N)]+[X[:,j]/D[h] for h in range(H) for j in range(n)])
        c=np.linalg.lstsq(F,y,rcond=1e-13)[0];res=F@c-y
        val=res@res
        if not gradient:return val,c,D,F,res,W
        grad=np.empty((H,n))
        for h in range(H):
            num=X@c[1+h*n:1+(h+1)*n]
            for j in range(n):
                dF=-num*Z[h][:,j+1]*W[h,j+1]/D[h]**2
                grad[h,j]=2*res@dF
        return val,grad.ravel()
    count=0
    while count<a.starts and time.monotonic()-started<a.seconds:
        scale=[1.,3.,8.,15.][count%4]
        init=rng.normal(size=H*n)*scale
        opt=minimize(calc,init,jac=True,method='L-BFGS-B',bounds=[(-35,35)]*(H*n),options={'maxiter':3000,'ftol':1e-15,'gtol':1e-10,'maxls':40})
        val,c,D,F,res,W=calc(opt.x,False)
        rec={'orientation':orientations,'l2_error':float(np.sqrt(val)),'linfty_error':float(abs(res).max()),'theta':opt.x.tolist(),'positive_weights':W.tolist(),'linear_coeffs':c.tolist(),'singular_values':np.linalg.svd(F,compute_uv=False).tolist(),'score':(F@c).tolist(),'iterations':int(opt.nit),'success':bool(opt.success)}
        if best is None or val<best[0]:
            best=(val,rec);print(json.dumps({'n':n,'H':H,'orientation':orientations,'start':count,'l2_error':rec['l2_error'],'linfty_error':rec['linfty_error']}),flush=True)
        count+=1
    if best:records.append(best[1])
    open(a.out,'w').write(json.dumps({'warning':'Floating exploration only, not proof','n':n,'H':H,'target_index':int(ix),'records':records,'elapsed_seconds':time.monotonic()-started},indent=2)+'\n')
