#!/usr/bin/env python3
"""Exact finite check of the written local stability argument."""
from fractions import Fraction as F
from itertools import combinations, permutations, product

D = [[11 + ((7*j + 11*h + 3*j*h) % 23) for h in range(3)]
     for j in range(7)]
delta = F(1, 10**12)

def parity(p):
    return -1 if sum(p[i] > p[j] for i in range(len(p))
                     for j in range(i+1,len(p))) % 2 else 1

def det(A):
    return sum(parity(p) * prod(A[i][p[i]] for i in range(len(A)))
               for p in permutations(range(len(A))))

def prod(xs):
    z=F(1)
    for x in xs: z*=x
    return z

def interval_det(rows):
    lo=hi=F(0)
    for p in permutations(range(3)):
        a=prod(F(1)/(D[rows[i]][p[i]]+delta) for i in range(3))
        b=prod(F(1)/(D[rows[i]][p[i]]-delta) for i in range(3))
        if parity(p)>0: lo+=a;hi+=b
        else: lo-=b;hi-=a
    return lo,hi

V=[[F(1,x) for x in row] for row in D]
minors={I:det([V[j] for j in I]) for I in combinations(range(7),3)}
assert all(minors.values())
for I,v in minors.items():
    lo,hi=interval_det(I)
    assert (lo>0 if v>0 else hi<0), (I,lo,hi,v)

circuits=[]
for I in combinations(range(7),4):
    c=[(-1)**k * minors[I[:k]+I[k+1:]] for k in range(4)]
    circuits.append((I,c))

def feasible(sigma):
    for I,c in circuits:
        sg=[sigma[j]*(1 if a>0 else -1) for j,a in zip(I,c)]
        if all(x==sg[0] for x in sg): return False
    return True

count=sum(feasible(sigma) for sigma in product((-1,1),repeat=7))
assert count==44,count
print('PASS: 35 exact interval determinants; 44 of 128 strict words.')
