#!/usr/bin/env python3
"""Exhaustive integer butterfly identities and modular span rank checks.

The written upper bound plus the nonzero modular minors certifies the
reported dimensions over the rationals. No asymptotic head bound is claimed.
"""
import importlib.util
import itertools
import json
from pathlib import Path

p = Path(__file__).with_name("butterfly-rectangle-decoder-check.py")
s=importlib.util.spec_from_file_location('bf',p);bf=importlib.util.module_from_spec(s);s.loader.exec_module(bf)
P=1000003

def rank(rows):
 piv={}
 for rr in rows:
  r=[x%P for x in rr]
  for i,v in sorted(piv.items()):
   if r[i]:
    c=r[i];r=[(a-c*b)%P for a,b in zip(r,v)]
  if any(r):
   i=next(i for i,x in enumerate(r) if x);v=pow(r[i],-1,P);piv[i]=[(x*v)%P for x in r]
 return len(piv)

def uh(d,k,g):
 return [0 if i>>(k+1)!=g else (1 if not i&(1<<k) else -1) for i in range(1<<d)]
def vh(d,k,s):
 return [0 if i&((1<<k)-1)!=s else (1 if not i&(1<<k) else -1) for i in range(1<<d)]
for d in range(1,4):
 h=1<<d; rows=[]
 for bits in itertools.product((0,1),repeat=len(bf.switches(d))):
  pi=bf.permutation(d,bits)
  rows.append([int(pi[i]==j)-int(i==j) for i in range(h) for j in range(h)])
  for k,s,g in bf.switches(d):
   u=uh(d,k,g);v=vh(d,k,s)
   assert sum(u[i]*v[pi[i]] for i in range(h))==2-4*bits[bf.switches(d).index((k,s,g))]
  for a in range(d):
   for b in range(a):
    for g in range(h>>(a+1)):
     for s in range(1<<b):
      u=uh(d,a,g);v=vh(d,b,s)
      assert sum(u[i]*v[pi[i]] for i in range(h))==0
 r=rank(rows);assert r==h*h-h-d*h//2
 print(json.dumps(dict(d=d,H=h,dimension=r,lower_wavelet_blocks_vanish=True,diagonal_signs_exact=True)))
