#!/usr/bin/env python3
"""Exact finite audit of the reflection-symmetric Cauchy lift.

This checks a 12-point limiting sign construction, not an asymptotic
head-complexity bound. See continuation-reflection-cauchy-lift.tex.
"""
from fractions import Fraction as F
from itertools import product

S=[[-1,1,-1,1],[-1,-1,1,1],[-1,-1,-1,-1]]
c=[1,-1,-1,1]
T=[[S[i][h]*c[h] for h in range(4)] for i in range(3)]
z=list(map(F,[1,2,3,4]))
qs=[[F(1)+2*t,F(-2)-3*t,F(1),t] for t in [F(-1),F(-3,5),F(-1,4),F(1)]]

def solve(A,b):
    m=[list(map(F,row))+[F(v)] for row,v in zip(A,b)]
    n=len(m[0])-1
    for col in range(n):
        row=next(i for i in range(col,len(m)) if m[i][col])
        m[col],m[row]=m[row],m[col]
        p=m[col][col];m[col]=[a/p for a in m[col]]
        for i in range(len(m)):
            if i!=col:
                p=m[i][col];m[i]=[a-p*b for a,b in zip(m[i],m[col])]
    assert all(not any(row[:n]) and row[n]==0 for row in m[n:])
    return [m[i][n] for i in range(n)]

def dot(a,b):return sum(x*y for x,y in zip(a,b))

def sign(v):return tuple(1 if x>0 else -1 for x in v)

assert len({sign(q) for q in qs})==4
assert all(dot(q,[1]*4)==dot(q,z)==0 and all(q) for q in qs)
usage=[0]*4
for fflat in product([-1,1],repeat=12):
    fs=[fflat[4*l:4*l+4] for l in range(3)]
    qi=next(k for k,q in enumerate(qs) if all(sign(q)!=f and tuple(-v for v in sign(q))!=f for f in fs))
    usage[qi]+=1;q=qs[qi]
    # A quadratic projection onto q-perp supplies a nonaffine vector unless
    # q annihilates z^2; in that case z^2 itself is already suitable.
    p=[v*v for v in z]
    if dot(q,p):
        # Correct coordinate 0, then ensure the resulting p is nonaffine.
        p[0]-=dot(q,p)/q[0]
    try:solve([[1,z[a],p[a]] for a in range(4)],[0]*4)
    except StopIteration:
        p=[v**3 for v in z];p[0]-=dot(q,p)/q[0]
    assert dot(q,p)==0
    coeff=[]
    for f in fs:
        a=[q[i]*f[i] for i in range(4)]
        P=sum(t for t in a if t>0);N=-sum(t for t in a if t<0)
        assert P>0 and N>0
        scores=[f[i]*(N if a[i]>0 else P) for i in range(4)]
        coeff.append(solve([[1,z[a],p[a]] for a in range(4)],scores))
    # Perturb each cubic-lift coefficient inside the strict feasible set.
    for k in range(1,20):
        delta=[F(k**(l+1),100000*(1+k**3)*(1+max(abs(v) for v in p))) for l in range(3)]
        w=[coeff[l][2]+delta[l] for l in range(3)]
        u=solve([T[l][:3] for l in range(3)],w)+[F(0)]
        if len(set(u))==4:break
    else:raise AssertionError('generic perturbation failed')
    u=[v+1-min(u) for v in u]
    assert min(u)>0 and len(set(u))==4
    assert [dot(T[l],u) for l in range(3)]==w
    for l in range(3):
        assert all(fs[l][a]*(coeff[l][0]+coeff[l][1]*z[a]+w[l]*p[a])>0 for a in range(4))
print('All 4096 sign tables verified; circuit-choice usage:',usage)
print('Every witness has positive distinct square tokens and exact strict limiting signs.')
