#!/usr/bin/env python3
"""Floating probe of one-minority-contact full-cube basis charts; run via heavy."""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=10);p.add_argument('--seconds',type=int,default=300);p.add_argument('--output',type=Path,required=True);p.add_argument('--seed',type=int,default=417326);args=p.parse_args()
n=args.n;d=n+1;N=2**n;rng=np.random.default_rng(args.seed)
X=np.array([[1]+[(j>>(n-1-i))&1 for i in range(n)]for j in range(N)],dtype=float)
start=time.monotonic();trials=0;ranked=0;tested=0;records=[]; best=1.0
while time.monotonic()-start<args.seconds:
 trials+=1
 w=rng.integers(1,32,size=n)
 if trials%2:w*=rng.choice([-1,1],size=n)
 w=np.r_[-int(w.sum()/2)+rng.integers(-4,5),w]
 vals=X@w;zeros=np.flatnonzero(vals==0)
 if len(zeros)<n or np.linalg.matrix_rank(X[zeros])<n:continue
 ranked+=1
 positive=np.flatnonzero(vals>0)
 if not len(positive):continue
 minimum=float(vals[positive].min())
 candidates=positive[(vals[positive]>minimum)&(vals[positive]<=3*minimum)]
 if not len(candidates):continue
 for q in rng.choice(candidates,size=min(12,len(candidates)),replace=False):
  tested+=1
  C=vals[positive,None]*X[q]-vals[q]*X[positive]
  # Maximize minimum coefficient, normalized sum=1.
  matrix=np.block([[-C,np.zeros((len(C),1))],[-np.eye(d),np.ones((d,1))]])
  lp=linprog(np.r_[np.zeros(d),-1],A_ub=matrix,b_ub=np.zeros(len(C)+d),A_eq=[np.r_[np.ones(d),0]],b_eq=[1],bounds=[(0,None)]*(d+1),method='highs')
  if not lp.success or lp.x[-1]<1e-7:continue
  balance=linprog(np.r_[-1,np.zeros(n)],A_ub=-C,b_ub=np.zeros(len(C)),A_eq=[np.ones(d)],b_eq=[1],bounds=[(0,None)]*d,method='highs')
  record={'trial':trials,'w':w.tolist(),'q':int(q),'Fq':float(vals[q]),'minimum_positive_F':minimum,'zeros':zeros.tolist(),'b':lp.x[:-1].tolist(),'min_b':float(lp.x[-1]),'max_b0':float(balance.x[0]),'balanced_b':balance.x.tolist()}
  if balance.x[0]<best-1e-8:
   best=float(balance.x[0]); records.append(record);print(record,flush=True)
  break
args.output.write_text(json.dumps({'status':'floating exploratory evidence only','n':n,'trials':trials,'full_rank_zero_flats':ranked,'candidate_contacts':tested,'records':records},indent=2)+'\n')
print({'trials':trials,'ranked':ranked,'tested':tested,'found':len(records)},flush=True)
