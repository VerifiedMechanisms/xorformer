#!/usr/bin/env python3
"""Exact finite evidence for spliced moment circuits; not a proof of all sizes."""
from fractions import Fraction as F
from itertools import product
from math import prod
import json

PRIME=1000000007

def rank_mod(rows,p=PRIME):
    a=[[int(v)%p for v in row] for row in rows]
    if not a: return 0
    r=0
    for j in range(len(a[0])):
        k=next((k for k in range(r,len(a)) if a[k][j]),None)
        if k is None: continue
        a[r],a[k]=a[k],a[r]
        inv=pow(a[r][j],-1,p)
        a[r]=[(v*inv)%p for v in a[r]]
        for k in range(r+1,len(a)):
            if a[k][j]:
                z=a[k][j]
                a[k]=[(v-z*w)%p for v,w in zip(a[k],a[r])]
        r+=1
        if r==len(a): break
    return r

def instance(n,D,M=2):
    q=D+1
    points=[]; coeff=[]
    points.append((0,)+tuple([1]*n)); coeff.append(F(1))
    for i in range(n):
        u=[1]+[int(j<i) for j in range(n)]
        v=u.copy();v[i+1]-=1
        if i:
            points.append(tuple(u));coeff.append(F(-1))
        points.append(tuple(v));coeff.append(F(1))
    for j in range(1,q+1):
        def L(t): return prod(F(t-k*M,(j-k)*M) for k in range(1,q+1) if k!=j)
        points.append((j*M,)+tuple([0]*n));coeff.append(-L(0)-L(1))
    assert len(points)==2*n+D+1 and len(set(points))==len(points)
    assert all(coeff)
    moment_rows=[];fiber_rows=[]
    for x in product((0,1),repeat=n):
        v=[w[0]+sum(a*b for a,b in zip(w[1:],x)) for w in points]
        for k in range(D+1):
            row=[a**k for a in v]
            assert sum(c*a for c,a in zip(coeff,row))==0
            moment_rows.append([pow(a,k,PRIME) for a in v])
        for a in sorted(set(v)):
            fiber_rows.append([int(b==a) for b in v])
    moment_rank=rank_mod(moment_rows)
    fiber_rank=rank_mod(fiber_rows)
    affine_rank=rank_mod([[a-b for a,b in zip(w,points[0])] for w in points[1:]])
    H=len(points)
    assert moment_rank==H-1 and fiber_rank==H and affine_rank==n+1
    return {'n':n,'D':D,'H':H,'exact_moments_verified':True,
      'all_coefficients_nonzero':True,'moment_rank_mod_prime':moment_rank,
      'fiber_rank_mod_prime':fiber_rank,'affine_rank_mod_prime':affine_rank,
      'prime':PRIME,'max_coefficient_bits':max(max(abs(c.numerator).bit_length(),c.denominator.bit_length()) for c in coeff)}

if __name__=='__main__':
    print(json.dumps([instance(n,D) for n,D in [(2,3),(2,10),(2,50),(3,4),(3,20),(4,5),(4,30),(5,6),(5,50)]],indent=2))
