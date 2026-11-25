#!/usr/bin/env python3
"""Numerical full-parameter actual-unit interpolation probe. Run with heavy."""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import least_squares
p=argparse.ArgumentParser();p.add_argument('--seconds',type=int,default=600);p.add_argument('--output',type=Path,required=True);p.add_argument('--seed',type=int,default=771035);p.add_argument('--n',type=int,default=5);p.add_argument('--heads',type=int,default=3);p.add_argument('--bias-free',action='store_true');a=p.parse_args();rng=np.random.default_rng(a.seed)
n=a.n;H=a.heads;N=2**n;X=np.array([[(x>>i)&1 for i in range(n)] for x in range(N)],float);q=n*H
free=int(a.bias_free);start=time.monotonic();trials=0;targets=0;roots=[];branches={};failures=0

def funjac(z,XX,orientation,target=None):
 bias=z[0] if free else 1.;aa=z[free:free+q].reshape(n,H);th=z[free+q:].reshape(n,H);p=np.exp(np.clip(th,-40,40));bb=np.where(orientation[None,:]>0,p,-p/(1+p.sum(axis=0)))
 B=np.where(orientation[None,:]>0,1+XX@bb,(1+(1-XX)@p)/(1+p.sum(axis=0)));A=XX@aa;vals=bias+(A/B).sum(axis=1)
 Ja=(XX[:,:,None]/B[:,None,:]).reshape(len(XX),q)
 dB=bb[None,:,:]*(XX[:,:,None]+np.where(orientation[None,None,:]>0,0,(XX@bb)[:,None,:]))
 Jb=(-A[:,None,:]*dB/B[:,None,:]**2).reshape(len(XX),q)
 return vals,np.c_[np.ones((len(XX),free)),Ja,Jb],bb

def save():
 a.output.write_text(json.dumps({'warning':'NUMERICAL_EXPLORATION_ONLY_NOT_PROOF','n':n,'heads':H,'bias_free':bool(free),'elapsed':time.monotonic()-start,'trials':trials,'targets':targets,'roots':roots,'failures':failures},indent=2)+'\n')

while time.monotonic()-start<a.seconds:
 targets+=1;J=np.sort(rng.choice(np.arange(0 if free else 1,N),2*q+free,replace=False));inactive=np.array([i for i in range(N) if i not in J]);XX=X[J]
 orientation=rng.choice([-1,1],H)
 z0=np.r_[rng.normal(size=q+free)*rng.uniform(.5,6),rng.uniform(-3,1,size=q)]
 f=np.where(funjac(z0,X,orientation)[0]>0,1.,-1.);target=f[J]
 if min(np.sum(target>0),np.sum(target<0))<n:continue
 # Avoid affine targets where exact unit fits have permanent rank deficiency.
 for attempt in range(18):
  if time.monotonic()-start>=a.seconds:break
  trials+=1;th=rng.uniform(-4,2,size=q)
  z=np.r_[np.zeros(q+free),th];_,Jac,_=funjac(z,XX,orientation);z[:q+free]=np.linalg.lstsq(Jac[:,:q+free],target-(0 if free else 1),rcond=None)[0]
  fit=least_squares(lambda z:funjac(z,XX,orientation)[0]-target,z,jac=lambda z:funjac(z,XX,orientation)[1],method='lm',max_nfev=500,ftol=1e-11,xtol=1e-11,gtol=1e-11)
  vals,jac,bb=funjac(fit.x,XX,orientation);err=float(np.max(np.abs(vals-target)))
  if err>1e-7:failures+=1;continue
  sv=np.linalg.svd(jac,compute_uv=False)
  if sv[-1]<1e-8 or np.max(np.abs(fit.x))>1e7:continue
  full,_,_=funjac(fit.x,X,orientation);val=float(np.min(np.abs(full[inactive])));key=(tuple(J),tuple(target))
  rec={'target_index':targets,'trial':trials,'inactive':inactive.tolist(),'basis':J.tolist(),'basis_labels':target.tolist(),'orientation':orientation.tolist(),'parameters':fit.x.tolist(),'denominator_slopes':bb.tolist(),'bias':float(fit.x[0]) if free else 1.,'numerator_slopes':fit.x[free:free+q].reshape(n,H).tolist(),'residual':err,'minimum_singular_value':float(sv[-1]),'inactive_value':val,'full_gap':float(np.min(np.abs(full))),'full_scores':full.tolist()}
  roots.append(rec);print({k:rec[k] for k in ['target_index','trial','inactive','residual','minimum_singular_value','inactive_value','full_gap']},flush=True);save()
  if abs(val)>=1-1e-6:
   old=branches.setdefault(key,{})
   sign=tuple(np.sign(full[inactive]).astype(int))
   if old and sign not in old:
    print('TWO_FULL_FEASIBLE_BRANCHES',list(old.values())[0],len(roots)-1,flush=True);save();raise SystemExit(0)
   old[sign]=len(roots)-1
save();print({'trials':trials,'targets':targets,'regular_roots':len(roots),'failures':failures,'elapsed':time.monotonic()-start},flush=True)
