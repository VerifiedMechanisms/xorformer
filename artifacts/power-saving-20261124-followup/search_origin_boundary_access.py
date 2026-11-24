#!/usr/bin/env python3
"""Finite LP exploration of origin-contact cone access to b0=0."""
import json,time,sys
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from sympy import Matrix
n=int(sys.argv[1])if len(sys.argv)>1 else 6;trials=int(sys.argv[2])if len(sys.argv)>2 else 100000
rng=np.random.default_rng(846731+n)
X=np.array([[1]+[(i>>(n-1-j))&1 for j in range(n)]for i in range(2**n)],dtype=int)
checked=0;max_lower=0;best=None;start=time.time()
for tr in range(trials):
 ids=np.r_[0,np.sort(rng.choice(np.arange(1,len(X)),n,replace=False))];V=X[ids]
 if abs(np.linalg.det(V))<.5:continue
 signs=np.r_[1,rng.choice([-1,1],n)];T=np.linalg.solve(V,signs[:,None]*V)
 bs=rng.integers(1,101,size=(32,n+1));aa=bs@T.T;av=aa@X.T;bv=bs@X.T
 good=np.flatnonzero(np.all(np.abs(av)>=bv-1e-7,axis=1))
 if not len(good):continue
 for j in good[:1]:
  f=np.where(av[j]>0,1,-1);C=f[:,None]*(X@T)-X
  lp=linprog(np.r_[1.,np.zeros(n)],A_ub=-C,b_ub=np.zeros(len(X)),A_eq=np.ones((1,n+1)),b_eq=[1],bounds=[(0,None)]*(n+1),method='highs')
  checked+=1
  if lp.success and lp.fun>max_lower+1e-8:
   max_lower=lp.fun;best={'basis':ids.tolist(),'signs':signs.tolist(),'b':bs[j].tolist(),'labels':(f>0).tolist(),'min_b0':lp.fun,'optimizer':lp.x.tolist(),'dual':lp.ineqlin.marginals.tolist(),'normalization_dual':lp.eqlin.marginals.tolist()}
   print(tr,checked,max_lower,flush=True)
  if max_lower>1e-6:break
 if max_lower>1e-6:break
out={'n':n,'trials':tr+1,'checked_chambers':checked,'largest_min_b0':max_lower,'candidate':best,'seconds':time.time()-start,'status':'floating LP exploration only'}
Path(f'artifacts/power-saving-20261124-followup/origin-boundary-access-n{n}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
