#!/usr/bin/env python3
"""Explore one-row mutations of feasible two-minority actual bases. Floating only."""
import argparse,json,itertools,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--seconds',type=int,default=300);args=p.parse_args();src=json.load(open(args.input));base=src['records'][-1];ids=base['basis'];n=len(ids)-1;d=n+1;N=2**n;neg=base['negative_positions'];X=np.array([[1]+list(x)for x in itertools.product([0,1],repeat=n)],dtype=float);g=np.ones(d);g[neg]=-1;rng=np.random.default_rng(713745)
start=time.monotonic();seen=set();best=2;records=[];charts=0;lps=0;pool=[ids];maxroots=0
while time.monotonic()-start<args.seconds:
 parent=pool[rng.integers(len(pool))];trial=list(parent);row=int(rng.integers(d));trial[row]=int(rng.integers(N));key=tuple(trial)
 if key in seen:continue
 seen.add(key);Z=X[trial]
 if abs(np.linalg.det(Z))<.5:continue
 charts+=1;Zi=np.linalg.inv(Z);T=Zi@np.diag(g)@Z;L=X@Zi[:,neg];roots=-L[:,1]/np.where(abs(L[:,0])>1e-9,L[:,0],np.nan);roots=sorted(set(round(float(t),10)for t in roots if np.isfinite(t)and t>1e-8));cuts=[0]+roots+[np.inf];feasible=[]
 for a,b in zip(cuts[:-1],cuts[1:]):
  r=(a+b)/2 if np.isfinite(b)else max(a*2,1);C=L[:,0]*r+L[:,1];f=np.where(C<=1e-7,1.,-1.);M=f[:,None]*(X@T)-X
  res=linprog(np.ones(d),A_ub=-M,b_ub=np.zeros(N),bounds=[(1,None)]*d,method='highs');lps+=1
  if res.success and np.min(M@res.x)>=-1e-7 and np.array_equal(np.sign(X@T@res.x),f):feasible.append({'interval':[a,None if not np.isfinite(b)else b],'denominator':res.x.tolist()})
 if len(feasible)>=2:
  pool.append(trial)
  if len(pool)>256:pool.pop(0)
 if len(feasible)>best or (len(feasible)==best and len(roots)>maxroots):
  best=len(feasible);maxroots=len(roots);rec={'basis':trial,'negative_positions':neg,'matrixT':T.tolist(),'branches':best,'roots':roots,'witnesses':feasible,'charts':charts,'lps':lps,'elapsed':time.monotonic()-start};records.append(rec);print('best',best,'roots',len(roots),'charts',charts,'lps',lps,flush=True)
args.output.write_text(json.dumps({'status':'floating exploration only','n':n,'charts':charts,'lps':lps,'pool_size':len(pool),'records':records},indent=2)+'\n')
