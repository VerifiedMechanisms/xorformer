#!/usr/bin/env python3
"""Floating search, with exact post-verification, of origin-contact charts. Run heavy."""
import argparse,json,time
from pathlib import Path
import numpy as np
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=6);p.add_argument('--seconds',type=int,default=600);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
n=args.n;d=n+1;N=2**n;rng=np.random.default_rng(891142)
X=np.array([[1]+[(x>>(n-1-i))&1 for i in range(n)] for x in range(N)],dtype=np.int64)
G=np.array([[1]+[2*((x>>i)&1)-1 for i in range(n)] for x in range(2**n)],dtype=np.int64)
start=time.monotonic();trials=0;uni=0;charts=0;feasible=0;found=[]
while time.monotonic()-start<args.seconds:
 trials+=1
 ids=np.r_[0,rng.choice(np.arange(1,N),size=n,replace=False)];Z=X[ids]
 det=round(np.linalg.det(Z))
 if abs(det)!=1:continue
 uni+=1;inv=np.rint(np.linalg.inv(Z)).astype(np.int64)
 if not np.array_equal(inv@Z,np.eye(d,dtype=int)):continue
 Ts=np.einsum('ij,gj,jk->gik',inv,G,Z);Us=np.einsum('xi,gij->gxj',X,Ts)
 # Integer positive denominators cover balanced and strongly boundary-biased cases.
 Bs=np.concatenate([rng.integers(1,12,size=(10,d)),np.ones((d,d),dtype=int)+1000*np.eye(d,dtype=int),np.ones((d,d),dtype=int)+1000000*np.eye(d,dtype=int)],axis=0)
 vals=np.einsum('gxj,bj->gbx',Us,Bs);dens=X@Bs.T
 ok=(np.abs(vals)>=dens.T[None,:,:]).all(axis=2)
 charts+=len(G);feasible+=int(ok.sum())
 bad=np.zeros_like(ok)
 first={}
 for gi,bi in np.argwhere(ok):
  if gi not in first:first[gi]=bi
  elif np.any((vals[gi,bi]>0)!=(vals[gi,first[gi]]>0)):bad[gi,bi]=True
 if bad.any():
  gi,bi=np.argwhere(bad)[0];b=Bs[bi];a=Ts[gi]@b;diff=np.where((vals[gi,bi]>0)!=(vals[gi,first[gi]]>0))[0]
  rec={'basis':ids.tolist(),'det':det,'labels':G[gi].tolist(),'denominator':b.tolist(),'numerator':a.tolist(),'other_denominator':Bs[first[gi]].tolist(),'other_numerator':(Ts[gi]@Bs[first[gi]]).tolist(),'different_vertices':diff.tolist(),'trial':trials,'unimodular_bases':uni,'full_cube_min_gap':int((np.abs(X@a)-X@b).min())}
  found.append(rec);print(rec,flush=True);break
report={'warning':'Integer candidate certificates; inverse checked by exact int64 arithmetic; no overflow at listed ranges. Search absence is not a theorem.','n':n,'elapsed':time.monotonic()-start,'trials':trials,'unimodular_bases':uni,'charts':charts,'feasible_witnesses':feasible,'found':found}
args.output.write_text(json.dumps(report,indent=2)+'\n');print(report if not found else {k:report[k] for k in ['elapsed','trials','unimodular_bases','charts','feasible_witnesses']},flush=True)
