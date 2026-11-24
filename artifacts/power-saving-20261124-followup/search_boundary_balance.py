#!/usr/bin/env python3
"""Exploratory floating LP search, emphasizing denominator boundary branches.
Run under heavy. Outputs are not formal or exact certificates.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=10);p.add_argument('--seconds',type=int,default=600);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
rng=np.random.default_rng(893012); n=a.n;d=n+1;N=2**n
X=np.array([[1]+[(x>>(n-1-i))&1 for i in range(n)] for x in range(N)],float)
start=time.monotonic();trials=0;best=1.;records=[]
while time.monotonic()-start<a.seconds:
 trials+=1
 w=rng.normal(size=d)*np.exp(rng.uniform(0,4,size=d)); w[0]=-w[1:].sum()/2+rng.normal()*np.linalg.norm(w[1:])*.2
 f=np.where(X@w>0,1.,-1.)
 b=np.exp(rng.uniform(-14,0,size=d)); b[0]=10**rng.uniform(-10,-3); b/=b.sum()
 objective=(f[:,None]*X).sum(axis=0)+rng.normal(size=d)*.001
 fit=linprog(objective,A_ub=-f[:,None]*X,b_ub=-X@b,bounds=[(None,None)]*d,method='highs')
 if not fit.success:continue
 residual=f*(X@fit.x)-X@b
 if residual.min() < -1e-7:continue
 active=np.flatnonzero(np.abs(residual)<1e-7); ids=[]
 for i in active:
  if np.linalg.matrix_rank(X[ids+[i]])>len(ids):ids.append(int(i))
  if len(ids)==d:break
 if len(ids)<d:continue
 T=np.linalg.solve(X[ids],f[ids,None]*X[ids]); U=X@T
 constraints=f[:,None]*U-X
 balance=linprog(np.r_[-1.,np.zeros(d-1)],A_ub=-constraints,b_ub=np.zeros(N),A_eq=np.ones((1,d)),b_eq=[1.],bounds=[(0,None)]*d,method='highs')
 if not balance.success:continue
 value=float(balance.x[0])
 if value < 1e-7:continue
 if value < best-1e-6:
  best=value
  record={'trial':trials,'elapsed':time.monotonic()-start,'basis':ids,'basis_labels':f[ids].tolist(),'full_labels':f.tolist(),'max_b0':value,'original_b':b.tolist(),'balanced_b':balance.x.tolist(),'matrix':T.tolist(),'original_min_gap':float((constraints@b).min())}
  records.append(record); print(json.dumps({k:record[k] for k in ['trial','elapsed','basis','max_b0','original_min_gap']}),flush=True)
  a.output.write_text(json.dumps({'warning':'Floating LP exploration, not an exact certificate','n':n,'trials':trials,'records':records},indent=2)+'\n')
a.output.write_text(json.dumps({'warning':'Floating LP exploration, not an exact certificate','n':n,'trials':trials,'records':records},indent=2)+'\n')
