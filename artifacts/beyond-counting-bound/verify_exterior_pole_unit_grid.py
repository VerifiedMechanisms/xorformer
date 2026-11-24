#!/usr/bin/env python3
"""Exact finite replay of exterior-pole-unit-grid.md; no solver is used."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def rootpoly(roots):
    p=[1]
    for x in roots: p=mul(p,[-x,1])
    return p

counts={"generating_coefficients":0,"run_lengths":0,"root_differences":0,
        "exact_head_values":0,"positive_denominators":0}
for h in range(1,101):
    signs=[-1 if i%4 in (0,3) else 1 for i in range(2*h)]
    series=[0]*(2*h-1)
    for j in range(h): series[2*j]=(-1)**j
    assert mul([-1,1],series)==signs
    assert signs[::-1]==[(-1)**h*x for x in signs]
    assert signs.count(1)==signs.count(-1)==h
    counts["generating_coefficients"]+=len(signs)
    lengths=[]
    for s in signs:
        if not lengths or s!=last: lengths.append(1)
        else: lengths[-1]+=1
        last=s
    assert lengths==[1]+[2]*(h-1)+[1]
    counts["run_lengths"]+=len(lengths)

for h,expected in ((2,[-2,0,0]),(3,[10,-5,1,0])):
    signs=[-1 if i%4 in (0,3) else 1 for i in range(2*h)]
    qm=rootpoly(i for i,s in enumerate(signs) if s==-1)
    qp=rootpoly(i for i,s in enumerate(signs) if s==1)
    assert [a-b for a,b in zip(qm,qp)]==expected
    counts["root_differences"]+=1
assert (-5)**2-4*10==-15

for x in (0,1):
    for y in (0,1):
        t=x+2*y; left=1+t; right=4-t
        assert left>0 and right>0
        value=F(5)-F(24,5*left)-F(24,5*right)
        assert value==(-1 if x==y else 1)
        counts["positive_denominators"]+=2
        counts["exact_head_values"]+=1

root=Path(__file__).resolve().parent
paths=[root/'exterior-pole-unit-grid.md',Path(__file__).resolve()]
result={"status":"PASS","scope":"finite exact checks supporting a written proof; not Lean",
        "counts":counts,"sha256":{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}
(root/'exterior-pole-unit-grid-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
