#!/usr/bin/env python3
"""Floating exploratory search; output is not a proof. Run under heavy."""
import argparse,json,time
import numpy as np
from scipy.optimize import linprog
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--seconds',type=int,default=300);p.add_argument('--n',type=int,default=8);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
rng=np.random.default_rng(239852);n=a.n;d=n+1;N=2**n
X=np.array([[1]+[(x>>(n-1-i))&1 for i in range(n)]for x in range(N)],float)
start=time.monotonic();best=0;trials=0;records=[]
while time.monotonic()-start<a.seconds:
    trials+=1
    w=rng.normal(size=d);w[0]=-w[1:].sum()/2+rng.normal()
    f=np.where(X@w>0,1.,-1.)
    b=np.exp(rng.normal(size=d));b/=b.sum()
    obj=(f[:,None]*X).sum(axis=0)+rng.normal(size=d)*.01
    z=linprog(obj,A_ub=-f[:,None]*X,b_ub=-X@b,bounds=[(None,None)]*d,method='highs')
    if not z.success:continue
    act=np.flatnonzero(np.abs(f*(X@z.x)-X@b)<1e-7)
    if len(act)<d:continue
    ids=[]
    for i in act:
        if np.linalg.matrix_rank(X[ids+[i]])>len(ids):ids.append(int(i))
        if len(ids)==d:break
    if len(ids)<d:continue
    T=np.linalg.solve(X[ids],f[ids,None]*X[ids])
    U=X@T
    mixed=np.flatnonzero((U.min(axis=1)<-1e-7)&(U.max(axis=1)>1e-7))
    # Uniform simplex and logarithmic scales, including the initial feasible point.
    B=np.c_[b,rng.dirichlet(np.ones(d),size=500).T,rng.dirichlet(np.full(d,.15),size=500).T]
    scores=U@B;denoms=X@B
    feasible=np.all(np.abs(scores)>=denoms-1e-7,axis=0)
    labs=np.unique((scores[:,feasible]>0).T,axis=0)
    count=len(labs)
    if count>best:
        best=count
        record={'trials':trials,'seconds':time.monotonic()-start,'basis':ids,'labels':f[ids].tolist(),'matrix':T.tolist(),'mixed_rows':mixed.tolist(),'sampled_branches':int(count),'initial_b':b.tolist(),'feasible_b':B[:,feasible].T[:50].tolist()}
        records.append(record)
        a.output.write_text(json.dumps({'warning':'Floating exploration only','n':n,'records':records},indent=2)+'\n')
        print(json.dumps({k:record[k]for k in ['trials','seconds','basis','sampled_branches']}|{'mixed_rows':len(mixed)}),flush=True)
a.output.write_text(json.dumps({'warning':'Floating exploration only','n':n,'trials':trials,'seconds':time.monotonic()-start,'records':records},indent=2)+'\n')
