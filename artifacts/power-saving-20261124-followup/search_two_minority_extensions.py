#!/usr/bin/env python3
"""Try appending positive unit contacts to a fixed two-minority chart.
Floating LP discovery only; exact certificate checking is separate. Run via heavy.
"""
import argparse,itertools,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--seconds',type=int,default=300);args=p.parse_args()
src=json.load(open(args.input));base=src['records'][-1]if'records'in src else src;nold=len(base['basis'])-1;n=nold+1;d=n+1;N=2**n;X=np.array([[1]+list(x)for x in itertools.product([0,1],repeat=n)],dtype=float);neg=base.get('negative_positions',[2,3]);start=time.monotonic();best=0;records=[];lps=0;tested=0
for anchor in range(2**nold):
 if time.monotonic()-start>args.seconds:break
 ids=[2*i for i in base['basis']]+[2*anchor+1];Z=X[ids];Zi=np.linalg.inv(Z);g=np.ones(d);g[neg]=-1;T=Zi@np.diag(g)@Z;L=X@Zi[:,neg];roots=-L[:,1]/np.where(abs(L[:,0])>1e-9,L[:,0],np.nan);roots=sorted(set(round(float(t),10)for t in roots if np.isfinite(t)and t>1e-8));cuts=[0]+roots+[np.inf];feasible=[];tested+=1
 for a,b in zip(cuts[:-1],cuts[1:]):
  r=(a+b)/2 if np.isfinite(b)else max(a*2,1);C=L[:,0]*r+L[:,1];f=np.where(C<=1e-7,1.,-1.);M=f[:,None]*(X@T)-X
  res=linprog(np.ones(d),A_ub=-M,b_ub=np.zeros(N),bounds=[(1,None)]*d,method='highs');lps+=1
  if res.success and np.min(M@res.x)>=-1e-7 and np.array_equal(np.sign(X@T@res.x),f):feasible.append({'interval':[a,None if not np.isfinite(b)else b],'denominator':res.x.tolist()})
 if len(feasible)>best:
  best=len(feasible);rec={'anchor':anchor,'basis':ids,'negative_positions':neg,'matrixT':T.tolist(),'branches':best,'witnesses':feasible};records.append(rec);print('anchor',anchor,'branches',best,'lps',lps,flush=True)
args.output.write_text(json.dumps({'status':'floating exploration only','n':n,'anchors_tested':tested,'lps':lps,'elapsed':time.monotonic()-start,'records':records},indent=2)+'\n')
