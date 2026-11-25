#!/usr/bin/env python3
"""Floating exploration only: full-cube k=2 actual-unit-basis branch LPs.
Run through heavy. Every claimed witness needs exact independent checking.
"""
import argparse,json,time,itertools
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=7);p.add_argument('--seconds',type=int,default=300);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
n=args.n;d=n+1;N=2**n;rng=np.random.default_rng(7426141);X=np.array([[1]+list(x)for x in itertools.product([0,1],repeat=n)],dtype=float)
start=time.monotonic();charts=0;lps=0;best=0;records=[];total_feasible=0
while time.monotonic()-start<args.seconds:
 ids=rng.choice(N,d,replace=False);Z=X[ids]
 if abs(np.linalg.det(Z))<.5:continue
 charts+=1;Zi=np.linalg.inv(Z);g=np.ones(d);neg=rng.choice(d,2,replace=False);g[neg]=-1
 T=Zi@np.diag(g)@Z;L=X@Zi[:,neg]
 roots=-L[:,1]/np.where(abs(L[:,0])>1e-9,L[:,0],np.nan)
 roots=sorted(set(round(float(t),10)for t in roots if np.isfinite(t)and t>1e-8))
 cuts=[0]+roots+[np.inf];feasible=[]
 for a,b in zip(cuts[:-1],cuts[1:]):
  if time.monotonic()-start>=args.seconds:break
  r=(a+b)/2 if np.isfinite(b) else max(a*2,1)
  C=L[:,0]*r+L[:,1];f=np.where(C<=1e-7,1.,-1.)
  # Feasibility cone at this label branch; prescribed basis identities exact algebraically.
  M=f[:,None]*(X@T)-X
  res=linprog(np.zeros(d),A_ub=-M,b_ub=np.zeros(N),bounds=[(1,None)]*d,method='highs')
  lps+=1
  if not res.success:continue
  den=res.x
  if np.min(M@den)<-1e-7:continue
  total_feasible+=1;actual=np.sign(X@T@den)
  if not np.array_equal(actual,f):continue
  feasible.append({'interval':[a,None if not np.isfinite(b)else b],'denominator':den.tolist(),'minimum_slack':float((M@den).min())})
 if len(feasible)>best:
  best=len(feasible);rec={'charts':charts,'lps':lps,'elapsed':time.monotonic()-start,'branches':best,'basis':ids.tolist(),'negative_positions':neg.tolist(),'matrixT':T.tolist(),'witnesses':feasible};records.append(rec);print({k:rec[k]for k in ['charts','lps','elapsed','branches']},flush=True);args.output.write_text(json.dumps({'status':'floating exploration in progress','n':n,'charts':charts,'lps':lps,'total_feasible':total_feasible,'records':records},indent=2)+'\n')
args.output.write_text(json.dumps({'status':'floating exploration only','n':n,'charts':charts,'lps':lps,'total_feasible':total_feasible,'records':records},indent=2)+'\n')
