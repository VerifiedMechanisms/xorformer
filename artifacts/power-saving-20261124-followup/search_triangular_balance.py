#!/usr/bin/env python3
"""Floating exploration of unimodular actual Boolean bases. Use heavy."""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=12);p.add_argument('--seconds',type=int,default=600);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
n=args.n;d=n+1;N=2**n;rng=np.random.default_rng(774811)
X=np.array([[1]+[(x>>(n-1-i))&1 for i in range(n)] for x in range(N)],float)
start=time.monotonic();trials=0;feasible=0;best=1.;records=[]
while time.monotonic()-start<args.seconds:
 trials+=1
 V=np.triu(rng.integers(0,2,size=(n,n)),1)+np.eye(n,dtype=int)
 Z=np.zeros((d,d));Z[:,0]=1;Z[1:,1:]=V
 g=rng.choice([-1,1],size=d);T=np.rint(np.linalg.solve(Z,g[:,None]*Z));U=X@T
 b=np.exp(rng.uniform(-4,0,size=d))*1e-5;b[rng.integers(1,d)]=1.;b/=b.sum()
 vals=U@b;f=np.where(vals>0,1.,-1.);C=f[:,None]*U-X
 if (C@b).min() < -1e-9:continue
 feasible+=1
 fit=linprog(np.r_[-1.,np.zeros(d-1)],A_ub=-C,b_ub=np.zeros(N),A_eq=np.ones((1,d)),b_eq=[1.],bounds=[(0,None)]*d,method='highs')
 if not fit.success:continue
 value=float(fit.x[0])
 if value<best-1e-7:
  best=value;ids=[int(sum(int(v)*2**(n-1-i) for i,v in enumerate(row[1:]))) for row in Z]
  rec={'trial':trials,'elapsed':time.monotonic()-start,'basis':ids,'basis_labels':g.tolist(),'full_labels':f.tolist(),'max_b0':value,'original_b':b.tolist(),'balanced_b':fit.x.tolist(),'matrix':T.tolist(),'original_min_gap':float((C@b).min())}
  records.append(rec);print({k:rec[k] for k in ['trial','elapsed','basis','max_b0']},flush=True)
  args.output.write_text(json.dumps({'warning':'Floating exploration, not exact certificate','n':n,'trials':trials,'feasible':feasible,'records':records},indent=2)+'\n')
args.output.write_text(json.dumps({'warning':'Floating exploration, not exact certificate','n':n,'trials':trials,'feasible':feasible,'records':records},indent=2)+'\n')
print({'trials':trials,'feasible':feasible,'best':best},flush=True)
