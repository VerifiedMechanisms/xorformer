#!/usr/bin/env python3
"""Exact identity checks and all 4096 finite eight-wire row ranks."""
import importlib.util
from pathlib import Path
import sympy as sy
from flint import fmpq_mat
from fractions import Fraction as F
path=Path(__file__).parent
sp=importlib.util.spec_from_file_location('bf',path/'butterfly-rectangle-decoder-check.py')
bf=importlib.util.module_from_spec(sp);sp.loader.exec_module(bf)
r,s,u,v,w,S,T=sy.symbols('r s u v w S T')
U=lambda x:u*x*x+v*x+w
P=lambda x:x*x-S*x+T
A=-u*S-v;B=u*T-w
assert sy.expand(U(r)*P(s)-U(s)*P(r)-(r-s)*(A*(r*s-T)+B*(r+s-S)))==0
x,y=sy.symbols('x y');L=(x*y-r*s)/(x+y-r-s)
assert sy.factor(sy.diff(L,r)-(x-s)*(y-s)/(x+y-r-s)**2)==0
sw=bf.switches(3);blocks=sorted(set((k,g) for k,s,g in sw))
p=[F(y&1,10)+F((y>>1)&1,100)+F((y>>2)&1,10000) for y in range(8)]
t=[F(1)-p[s] for s in range(4)]
for word in range(1<<len(sw)):
 bits=[(word>>e)&1 for e in range(len(sw))];pi=bf.permutation(3,bits)
 rows=[]
 for k,s,g in sw:
  row=[F(0)]*8
  for h in range(8):
   if h>>(k+1)==g:row[pi[h]]=F(1 if not h&(1<<k) else -1)/(t[s]-p[pi[h]])
  rows.append(row+[F(b==(k,g)) for b in blocks])
 assert fmpq_mat([[str(v) for v in row] for row in rows]).rank()==12
print('PASS: exact quadratic and derivative identities, and rank twelve for all 4096 rational butterfly settings')
