#!/usr/bin/env python3
"""Exploratory positive full-unit branch counts for ill-conditioned Boolean bases.
Run via heavy. Counts from floating samples are not a theorem.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=10);p.add_argument('--seconds',type=int,default=300);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
rng=np.random.default_rng(984712);n=args.n;d=n+1;N=2**n
X=np.array([[1]+[(u>>(n-1-i))&1 for i in range(n)] for u in range(N)],dtype=np.int64)
start=time.monotonic();trials=0;records=[];best=0
while time.monotonic()-start<args.seconds:
 trials+=1
 V=np.eye(n,dtype=np.int64)
 # Greedily maximize each new inverse column by choosing positive or negative
 # previous entries; mix in random triangular simplices for diversity.
 for j in range(1,n):
  if trials%3:
   Vi=np.rint(np.linalg.inv(V)).astype(np.int64)
   row=rng.integers(j);sign=rng.choice([-1,1]);V[:j,j]=(sign*Vi[row,:j]>0)
   if not V[:j,j].any():V[rng.integers(j),j]=1
  else:V[:j,j]=rng.integers(0,2,size=j)
 Z=np.zeros((d,d),dtype=np.int64);Z[:,0]=1;Z[1:,1:]=V
 Zi=np.rint(np.linalg.inv(Z)).astype(np.int64)
 if not np.array_equal(Zi@Z,np.eye(d,dtype=np.int64)):continue
 signs=rng.choice([-1,1],size=d);T=Zi@np.diag(signs)@Z;M=X@T
 seen={};feasible=0
 for batch in range(24):
  count=384
  bs=np.exp(rng.uniform(-rng.choice([3.,8.,20.]),0,size=(d,count)))
  bs/=bs.sum(axis=0)
  As=M@bs;Bs=X@bs
  # Fixed generous gap above floating tolerance. Basis contacts are identities.
  good=np.min(np.abs(As)-Bs,axis=0)>=-1e-11
  for j in np.flatnonzero(good):
   feasible+=1;bits=np.packbits(As[:,j]>0).tobytes()
   if bits not in seen:seen[bits]=bs[:,j].tolist()
  if time.monotonic()-start>args.seconds:break
 if len(seen)>best:
  best=len(seen);basis=[0]+[sum(int(V[j,i])<<(n-1-i) for i in range(n))for j in range(n)]
  rec={'trial':trials,'elapsed':time.monotonic()-start,'branches':best,'samples_feasible':feasible,'basis':basis,'signs':signs.tolist(),'matrixT':T.tolist(),'max_inverse':int(np.abs(Zi).max()),'representatives':list(seen.values())}
  records.append(rec);print({k:rec[k]for k in ['trial','elapsed','branches','samples_feasible','max_inverse']},flush=True)
args.output.write_text(json.dumps({'status':'floating exploratory evidence only','n':n,'trials':trials,'records':records},indent=2)+'\n')
