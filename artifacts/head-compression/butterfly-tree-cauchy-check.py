#!/usr/bin/env python3
"""Exact finite tree-decoder audit, with witnesses and exclusion certificates.

For every permutation and every sign pattern, either a strict rational
coefficient witness is checked or a nonzero signed row dependence with
nonnegative coefficients excludes the pattern.  This certifies complete
coverage even though the central arrangements are degenerate.
"""
import importlib.util,itertools,json
from pathlib import Path
from fractions import Fraction as F
spec=importlib.util.spec_from_file_location('e',Path(__file__).with_name('reverse-joint-affine-plane-search.py'))
e=importlib.util.module_from_spec(spec);spec.loader.exec_module(e)
def circuits(A):
 r=len(A);n=len(A[0]);out=[]
 for size in range(2,n+2):
  for ids in itertools.combinations(range(r),size):
   rows=[A[i] for i in ids];cols=e.independent_columns(rows[:-1])
   if len(cols)!=size-1:continue
   lam=e.solve([[rows[j][col] for j in range(size-1)] for col in cols],[-rows[-1][col] for col in cols])+[F(1)]
   if any(x==0 for x in lam):continue
   if any(sum(lam[j]*rows[j][col] for j in range(size)) for col in range(n)):continue
   mask=sum(1<<i for i in ids);pat=sum((x>0)<<i for i,x in zip(ids,lam))
   out.append((ids,lam,mask,pat))
 return out
pole=[F(1,100000)+F(x,10000000) for x in [-3,-1,1,3]]
sets=[set(range(4))]*4+[{1,3},{1,3},{2},{3}]
for alpha in [F(1,2),F(2),F(4)]:
 times=[F(99,100)+F(x,1000) for x in [-3,-1,1,3,-alpha,alpha,0,0]]
 covered=set();stats=[]
 for pi in itertools.permutations(range(4)):
  A=[[1/(t-pole[x])**2 if pi[x] in selected else F(0) for x in range(4)] for t,selected in zip(times,sets)]
  cs=circuits(A)
  good={pat for pat in range(256) if not any((pat&mask) in (bad,mask^bad) for ids,lam,mask,bad in cs)}
  found,simple=e.orthants(A,[F(0)]*8)
  assert set(found)==good,(pi,len(found),len(good))
  # The exact witness routine checks every covered orthant.  Independently
  # check a positive-dependence exclusion for every other sign pattern.
  for pat in set(range(256))-good:
   ids,lam,mask,bad=next(c for c in cs if (pat&c[2]) in (c[3],c[2]^c[3]))
   orient=1 if (pat&mask)==bad else -1
   positive=[orient*lam[j]*(1 if pat&(1<<i) else -1) for j,i in enumerate(ids)]
   assert all(x>0 for x in positive)
   assert all(sum(lam[j]*A[i][col] for j,i in enumerate(ids))==0 for col in range(4))
  covered.update(good);stats.append((pi,len(cs),len(good)))
 print(json.dumps({'alpha':str(alpha),'complete_coverage':len(covered),'missing':sorted(set(range(256))-covered),'per_permutation':stats}),flush=True)
