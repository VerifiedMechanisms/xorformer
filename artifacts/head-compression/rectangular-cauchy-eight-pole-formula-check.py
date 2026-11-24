#!/usr/bin/env python3
"""Solver-free Fraction audit of the elementary eight-pole formula."""
from fractions import Fraction as F
from itertools import product
from math import prod
cases=0
for t in [[F(77,80),F(39,40),F(79,80),F(1)], [F(1),F(2),F(3),F(4)], [F(3,2),F(5,3),F(7,3),F(9,2)]]:
 for scale in [10,100,10000,10**8]:
  e=t[0]/(8*scale);p=[(h+1)*e for h in range(8)]
  R=lambda z:(z-t[0])*(z-t[2])
  PA=lambda z:prod(z-p[h] for h in [0,6,7])
  PC=lambda z:prod(z-p[h] for h in [2,4,5])
  q0=(t[0]-2*e)*(t[0]-4*e);q2=(t[2]-2*e)*(t[2]-4*e);L=(q0+q2)/(t[2]-t[0])
  v=[F(0)]*8;v[3]=(q0+L*(t[0]-4*e))/(2*e);v[1]=v[3]+L
  B=lambda z:v[1]/(z-2*e)
  D=lambda z:v[3]/(z-4*e)
  S=lambda z:B(z)+D(z)+1
  k=lambda z:PC(z)/PA(z)
  assert k(t[1])>k(t[3])
  u=-PC(t[1])*S(t[1])/R(t[1]);w=PC(t[3])*S(t[3])/R(t[3]);alpha=(u+w)/(k(t[1])-k(t[3]));gamma=k(t[3])*alpha+w
  for ids,co in [([0,6,7],alpha),([2,4,5],gamma)]:
   for h in ids:v[h]=abs(co*R(p[h])/prod(p[h]-p[j] for j in ids if j!=h))
  assert min(v)>0
  for a,b,c,d in product([-1,1],repeat=4):
   tau=[a,b,c,d,-c,c,-a,a];word=[d,-a,b,c]
   score=[sum(tau[h]*v[h]/(z-p[h]) for h in range(8)) for z in t]
   assert min(w*z for w,z in zip(word,score))>=1
   cases+=1
print(f'PASS: {cases} exact four-query words from the explicit positive formulas.')
