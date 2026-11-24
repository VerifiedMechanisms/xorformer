#!/usr/bin/env python3
"""Exact finite checks for the two written shared-moment identities."""
from fractions import Fraction as F
from itertools import product, combinations
from math import factorial
from functools import reduce

count = 0
for H in range(2, 17):
    xx = [F(2*h-H+1, 2*H) for h in range(H)]
    aa = [1/reduce(lambda a,b:a*b,
                  [xx[h]-xx[g] for g in range(H) if g != h],F(1))
          for h in range(H)]
    for u in [F(-1,3), F(0), F(1,7), F(2,3)]:
        assert all(1+u*x>0 for x in xx)
        for k in range(1,H):
            if 2*k < H:
                assert sum(a*(1+u*x)**k*x**(k-1)
                           for a,x in zip(aa,xx)) == 0
                count += 1

for d in range(1, 8):
    xx = [F(j+1, d+2) for j in range(d)]
    signs = list(product([-1,1],repeat=d))
    pp = [sum(x*h for x,h in zip(xx,s)) for s in signs]
    for k in range(d+1):
        for S in combinations(range(d),k):
            chi = [reduce(lambda a,b:a*b,[s[j] for j in S],1) for s in signs]
            for l in range(k):
                assert sum(c*p**l for c,p in zip(chi,pp)) == 0
                count += 1
            answer = 2**d*factorial(k)*reduce(lambda a,b:a*b,[xx[j] for j in S],F(1))
            assert sum(c*p**k for c,p in zip(chi,pp)) == answer
            count += 1
print("Exact shared-moment checks passed:",count,"identities.")
