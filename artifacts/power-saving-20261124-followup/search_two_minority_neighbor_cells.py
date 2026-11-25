#!/usr/bin/env python3
"""Search for two feasible labels in one c_i=0,-r,-1 comparison cell.
Floating discovery only; exact checking required. Run via heavy.
"""
import argparse,json,itertools,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--seconds',type=int,default=300);p.add_argument('--seed',type=int,default=714954);p.add_argument('--include-constant',action='store_true');args=p.parse_args();src=json.load(open(args.input));base=src['records'][-1];n=len(base['basis'])-1;d=n+1;N=2**n;neg=base['negative_positions'];X=np.array([[1]+list(x)for x in itertools.product([0,1],repeat=n)],float);g=np.ones(d);g[neg]=-1;rng=np.random.default_rng(args.seed);pool=[base['basis']];seen=set();start=time.monotonic();charts=0;lps=0;records=[]
def roots_of(v):
 r=-v[:,1]/np.where(abs(v[:,0])>1e-8,v[:,0],np.nan)
 return sorted(set(round(float(t),10)for t in r if np.isfinite(t)and t>1e-8))
while time.monotonic()-start<args.seconds and not records:
 trial=list(pool[rng.integers(len(pool))]);trial[int(rng.integers(d))]=int(rng.integers(N));key=tuple(trial)
 if key in seen:continue
 seen.add(key);Z=X[trial]
 if abs(np.linalg.det(Z))<.5:continue
 charts+=1;Zi=np.linalg.inv(Z);coef=Zi[:,neg];L=X@coef;T=Zi@np.diag(g)@Z;tablecuts=[0]+roots_of(L)+[np.inf]
 # The original question concerns variable coefficients only.
 cc=coef if args.include_constant else coef[1:]
 nc=roots_of(np.vstack([cc,cc+np.array([1.,0.]),cc+np.array([0.,1.])]))
 cuts=[0]+sorted(set(tablecuts[1:-1]+nc))+[np.inf];good={};feas=0
 for a,b in zip(cuts[:-1],cuts[1:]):
  r=(a+b)/2 if np.isfinite(b)else max(a*2,1);f=np.where(L[:,0]*r+L[:,1]<=1e-7,1.,-1.);M=f[:,None]*(X@T)-X
  rows=[-M];rhs=[np.zeros(N)];q1=X[trial[neg[0]]];q2=X[trial[neg[1]]]
  if a>0:rows.append((a*q2-q1)[None,:]);rhs.append(np.array([-1.]))
  if np.isfinite(b):rows.append((q1-b*q2)[None,:]);rhs.append(np.array([-1.]))
  res=linprog(np.ones(d),A_ub=np.vstack(rows),b_ub=np.concatenate(rhs),bounds=[(1,None)]*d);lps+=1
  if not res.success or np.min(M@res.x)<-1e-6:continue
  rr=float(q1@res.x/(q2@res.x));sig=tuple(np.sign(np.round(np.r_[cc[:,0]*rr+cc[:,1],cc[:,0]*rr+cc[:,1]+rr,cc[:,0]*rr+cc[:,1]+1],7)).astype(int));bits=np.packbits(f>0).tobytes();feas+=1
  witness={'interval':[a,None if not np.isfinite(b)else b],'ratio':rr,'denominator':res.x.tolist(),'labels':f.astype(int).tolist()}
  if sig in good and good[sig][0]!=bits:
   records.append({'basis':trial,'negative_positions':neg,'matrixT':T.tolist(),'coefficient_pencil':coef.tolist(),'comparison_signature':sig,'witnesses':[good[sig][1],witness]});print('FOUND',charts,lps,flush=True);break
  good[sig]=(bits,witness)
 if feas>=2:
  pool.append(trial)
  if len(pool)>256:pool.pop(0)
args.output.write_text(json.dumps({'status':'floating discovery only','n':n,'include_constant':args.include_constant,'seed':args.seed,'charts':charts,'lps':lps,'pool_size':len(pool),'records':records},indent=2,default=lambda x: int(x))+'\n')
