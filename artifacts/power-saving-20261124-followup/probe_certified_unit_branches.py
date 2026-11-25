#!/usr/bin/env python3
"""Search for other unit-contact roots near the existing certified H3,n18 root."""
import argparse,json,time,itertools
from pathlib import Path
import numpy as np
from scipy.optimize import least_squares
p=argparse.ArgumentParser();p.add_argument('--seconds',type=int,default=600);p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--seed',type=int,default=611432);a=p.parse_args();rng=np.random.default_rng(a.seed)
d=json.loads(a.source.read_text());n=d['n'];H=d['heads'];q=n*H;scale=float(d['denominator']);z=np.array([int(v)/scale for v in d['center']]);score_scale=2/float(d['gamma']);aa=z[:q].reshape(n,H);bb=z[q:].reshape(n,H);th=np.log(-bb/(1+bb.sum(axis=0)));base=np.r_[aa.ravel(),th.ravel()]
J=np.array(d['active_vertices']);target=np.array(d['active_labels'],float);XX=((J[:,None]>>np.arange(n))&1).astype(float);N=2**n;probe_idx=np.r_[J,rng.choice(N,256,replace=False)];XP=((probe_idx[:,None]>>np.arange(n))&1).astype(float)

def funjac(z,X):
 aa=z[:q].reshape(n,H);p=np.exp(np.clip(z[q:].reshape(n,H),-25,25));T=1+p.sum(axis=0);bb=-p/T;B=(1+(1-X)@p)/T;A=X@aa;v=1+score_scale*(A/B).sum(axis=1)
 Ja=score_scale*(X[:,:,None]/B[:,None,:]).reshape(len(X),q);dB=bb[None,:,:]*(X[:,:,None]+(X@bb)[:,None,:]);Jb=score_scale*(-A[:,None,:]*dB/B[:,None,:]**2).reshape(len(X),q)
 return v,np.c_[Ja,Jb],bb

bp,_,_=funjac(base,XP);bv,bj,_=funjac(base,XX);print({'baseline_residual':float(np.max(abs(bv-target))),'minimum_singular_value':float(np.linalg.svd(bj,compute_uv=False)[-1])},flush=True)
start=time.monotonic();trials=0;regular=0;distinct=[];failed=0;fullX=None;basefull=None

def save():
 a.output.write_text(json.dumps({'warning':'NUMERICAL_EXPLORATION_ONLY_NOT_PROOF','source_branch':'origin/ar/7485202da367','source_path':'artifacts/beyond-counting-bound/unit-minimum-certificate/data.json','numerator_coordinate_scale':score_scale,'elapsed':time.monotonic()-start,'trials':trials,'regular':regular,'failed':failed,'distinct_roots':distinct},indent=2)+'\n')

while time.monotonic()-start<a.seconds:
 trials+=1;sig=10**rng.uniform(-6,1);zz=base.copy();zz[q:]+=rng.normal(size=q)*sig
 _,jac,_=funjac(zz,XX);zz[:q]=np.linalg.lstsq(jac[:,:q],target-1,rcond=None)[0]
 fit=least_squares(lambda z:funjac(z,XX)[0]-target,zz,jac=lambda z:funjac(z,XX)[1],method='lm',max_nfev=500,ftol=1e-11,xtol=1e-11,gtol=1e-11)
 vals,jac,b=funjac(fit.x,XX);err=float(np.max(abs(vals-target)))
 if err>1e-7:failed+=1;continue
 sv=float(np.linalg.svd(jac,compute_uv=False)[-1])
 if sv<1e-8:continue
 regular+=1;pv,_,_=funjac(fit.x,XP);distance=float(np.max(abs(pv-bp)))
 if distance<1e-4 or any(np.max(abs(pv-np.array(old['probe_values'])))<1e-4 for old in distinct):continue
 if fullX is None:
  fullX=((np.arange(N)[:,None]>>np.arange(n))&1).astype(float)
  ba=base[:q].reshape(n,H);pb=np.exp(base[q:].reshape(n,H));basefull=1+score_scale*((fullX@ba)/((1+(1-fullX)@pb)/(1+pb.sum(axis=0)))).sum(axis=1)
 aout=fit.x[:q].reshape(n,H);pout=np.exp(np.clip(fit.x[q:].reshape(n,H),-25,25));v=1+score_scale*((fullX@aout)/((1+(1-fullX)@pout)/(1+pout.sum(axis=0)))).sum(axis=1);changed=np.flatnonzero(np.sign(v)!=np.sign(basefull));gap=float(np.min(abs(v)))
 rec={'trial':trials,'perturbation':sig,'residual':err,'minimum_singular_value':sv,'probe_distance':distance,'full_gap':gap,'different_label_count':len(changed),'different_label_examples':changed[:100].tolist(),'parameters':fit.x.tolist(),'denominator_slopes':b.tolist(),'probe_values':pv.tolist()};distinct.append(rec);print({k:rec[k]for k in ['trial','residual','minimum_singular_value','probe_distance','full_gap','different_label_count']},flush=True);save()
 if gap>=1-1e-6 and len(changed):print('DISTINCT_FULL_UNIT_FEASIBLE_BRANCH',flush=True);break
save();print({'trials':trials,'regular':regular,'distinct':len(distinct),'failed':failed,'elapsed':time.monotonic()-start},flush=True)
