#!/usr/bin/env python3
"""Numerical unit-contact search on two Boolean block counts; run with heavy."""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import least_squares
p=argparse.ArgumentParser();p.add_argument('--seconds',type=int,default=600);p.add_argument('--output',type=Path,required=True);p.add_argument('--seed',type=int,default=995071);p.add_argument('--block',type=int,default=4);a=p.parse_args();rng=np.random.default_rng(a.seed)
m=a.block;n=2;H=2;q=4;X=np.array([(i,j)for i in range(m+1)for j in range(m+1)],float);N=len(X)
start=time.monotonic();trials=0;targets=0;roots=[];branches={};failures=0

def funjac(z,XX,orientation):
 aa=z[:q].reshape(n,H);th=z[q:].reshape(n,H);p=np.exp(np.clip(th,-25,25));T=1+m*p.sum(axis=0);bb=np.where(orientation[None,:]>0,p,-p/T)
 B=np.where(orientation[None,:]>0,1+XX@bb,(1+(m-XX)@p)/T);A=XX@aa;vals=1+(A/B).sum(axis=1)
 Ja=(XX[:,:,None]/B[:,None,:]).reshape(len(XX),q)
 dB=bb[None,:,:]*(XX[:,:,None]+np.where(orientation[None,None,:]>0,0,m*(XX@bb)[:,None,:]))
 Jb=(-A[:,None,:]*dB/B[:,None,:]**2).reshape(len(XX),q)
 return vals,np.c_[Ja,Jb],bb

def save():
 a.output.write_text(json.dumps({'warning':'NUMERICAL_EXPLORATION_ONLY_NOT_PROOF','block':m,'heads':H,'elapsed':time.monotonic()-start,'trials':trials,'targets':targets,'roots':roots,'failures':failures},indent=2)+'\n')
while time.monotonic()-start<a.seconds:
 targets+=1;J=np.sort(rng.choice(np.arange(1,N),8,replace=False));inactive=np.array([i for i in range(1,N) if i not in J]);XX=X[J]
 orientation=rng.choice([-1,1],H);z0=np.r_[rng.normal(size=q)*rng.uniform(.5,6),rng.uniform(-3,1,size=q)]
 f=np.where(funjac(z0,X,orientation)[0]>0,1.,-1.);f[0]=1.;target=f[J]
 if min(np.sum(target>0),np.sum(target<0))<2:continue
 seen=[]
 for attempt in range(24):
  if time.monotonic()-start>=a.seconds:break
  trials+=1;th=rng.uniform(-4,2,size=q);z=np.r_[np.zeros(q),th];_,Jac,_=funjac(z,XX,orientation);z[:q]=np.linalg.lstsq(Jac[:,:q],target-1,rcond=None)[0]
  fit=least_squares(lambda z:funjac(z,XX,orientation)[0]-target,z,jac=lambda z:funjac(z,XX,orientation)[1],method='lm',max_nfev=300,ftol=1e-11,xtol=1e-11,gtol=1e-11)
  vals,jac,bb=funjac(fit.x,XX,orientation);err=float(np.max(np.abs(vals-target)))
  if err>1e-7:failures+=1;continue
  sv=np.linalg.svd(jac,compute_uv=False)
  if sv[-1]<1e-8 or np.max(np.abs(fit.x))>1e7:continue
  full,_,_=funjac(fit.x,X,orientation)
  if any(np.max(np.abs(full-old))<1e-5 for old in seen):continue
  seen.append(full);gap=float(np.min(np.abs(full)));key=(tuple(J),tuple(target))
  rec={'target_index':targets,'trial':trials,'basis':XX.tolist(),'basis_labels':target.tolist(),'orientation':orientation.tolist(),'parameters':fit.x.tolist(),'denominator_slopes':bb.tolist(),'numerator_slopes':fit.x[:q].reshape(n,H).tolist(),'residual':err,'minimum_singular_value':float(sv[-1]),'full_gap':gap,'full_scores':full.tolist()}
  roots.append(rec);print({k:rec[k] for k in ['target_index','trial','basis','residual','minimum_singular_value','full_gap']},flush=True);save()
  if gap>=1-1e-6:
   old=branches.setdefault(key,{});sign=tuple(np.sign(full).astype(int))
   if old and sign not in old:
    print('TWO_FULL_FEASIBLE_BRANCHES',list(old.values())[0],len(roots)-1,flush=True);save();raise SystemExit(0)
   old[sign]=len(roots)-1
save();print({'trials':trials,'targets':targets,'regular_roots':len(roots),'failures':failures,'elapsed':time.monotonic()-start},flush=True)
