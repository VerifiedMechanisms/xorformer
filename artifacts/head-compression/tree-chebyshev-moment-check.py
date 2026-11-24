#!/usr/bin/env python3
"""Exact subset-moment audit in the power-of-two cyclotomic quotient.

Run as heavy python3 tree-chebyshev-moment-check.py.
This verifies finite cases of the written theorem, not a global bound.
"""
from itertools import combinations
from math import comb
import numpy as np
for H in (4,8,16):
 d=2*H
 def vec(terms):
  v=np.zeros(d,dtype=np.int64)
  for exp,c in terms:
   q,r=divmod(exp,d);v[r]+=c*((-1)**q)
  return v
 subsets=np.arange(1<<H,dtype=np.int64)
 unresolved=np.ones(1<<H,dtype=bool);unresolved[0]=False
 vals=np.full(1<<H,-1)
 for l in range(H):
  rows=[]
  for i in range(H):
   k=2*i+1
   terms=[]
   for j in range(l+1):
    cc=(-1)**i*comb(l,j)
    terms.extend([(k*(l-2*j+1),cc),(k*(l-2*j-1),-cc)])
   rows.append(vec(terms))
  sums=np.zeros((1<<H,d),dtype=np.int64)
  for m in range(1,1<<H):
   low=m&-m;i=low.bit_length()-1;sums[m]=sums[m^low]+rows[i]
  nonzero=np.any(sums!=0,axis=1);found=nonzero&unresolved
  vals[found]=l;unresolved[found]=False
  if not np.any(unresolved):break
 counts={int(k):int(np.sum(vals==k)) for k in set(vals)}
 expected={-1:1,H-1:1}
 j=0
 while 2**j<H:
  expected[2**j-1]=2**(H//(2**j))-2**(H//(2**(j+1)))
  j+=1
 assert counts==expected,(H,counts,expected)
 print(H,counts,flush=True)
 for size in range(1,H):
  vv={int(vals[sum(1<<i for i in S)]) for S in combinations(range(H),size)}
  if len(vv)>1:print(' size',size,'vals',vv)
