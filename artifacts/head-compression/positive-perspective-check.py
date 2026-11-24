#!/usr/bin/env python3
"""Exact rational sanity checks for the perspective reformulation."""
from fractions import Fraction as Q
from itertools import product
import json
import sympy as sp

B = ((Q(2), Q(3), Q(5)), (Q(7), Q(2), Q(1)))
U = ((Q(1), Q(2), Q(3)), (Q(2), Q(1), Q(4)))
shifts = (Q(3), Q(5))
C = Q(3)
bias = sum(shifts) - C
A = tuple(tuple(u*u-c*b for u,b in zip(us,bs))
          for us,bs,c in zip(U,B,shifts))

def vals(x):
    ys = ((Q(1), *x), (Q(1), *(1-z for z in x)))
    ds = [sum(b*y for b,y in zip(bs,yy)) for bs,yy in zip(B,ys)]
    orig = bias+sum(sum(a*y for a,y in zip(aa,yy))/d
                    for aa,yy,d in zip(A,ys,ds))
    ext = sum(sum(u*u*y*y for u,y in zip(us,yy))/d
              for us,yy,d in zip(U,ys,ds))-C
    q = [u*y for us,yy in zip(U,ys) for u,y in zip(us,yy)]
    mat = sp.diag(*[sp.Rational(d.numerator,d.denominator)
                    for d in ds for _ in range(3)], sp.Rational(C))
    for i,v in enumerate(q):mat[i,6]=mat[6,i]=sp.Rational(v)
    assert Q(mat.det()) == -ext*ds[0]**3*ds[1]**3
    t=Q(11)
    changed = sum(((u*u+t*b) if h==0 else u*u)*y*y/d
                  for h,(us,bs,yy,d) in enumerate(zip(U,B,ys,ds))
                  for u,b,y in zip(us,bs,yy)) - C-t
    gauge = -t*sum(b*y*(1-y) for b,y in zip(B[0],ys[0]))/ds[0]
    assert changed-ext == gauge
    return orig,ext,gauge

records=[]
for x in product((Q(0),Q(1)), repeat=2):
    orig,ext,gauge=vals(x)
    assert orig==ext and gauge==0
    records.append({'x':list(map(str,x)),'score':str(orig)})
for x in ((Q(1,2),Q(1,3)),(Q(0),Q(2,3)),(Q(1),Q(1,2))):
    orig,ext,gauge=vals(x)
    assert gauge<0
    records.append({'x':list(map(str,x)),'extension':str(ext),'gauge':str(gauge)})
print(json.dumps({'status':'passed exact rational checks','points':records},indent=2))
