#!/usr/bin/env python3
"""Exact finite tests for the strict reverse-grid axis repair identity."""
from fractions import Fraction as Q
from itertools import product
from random import Random

rng = Random(14804)
checked = 0
for r in range(1, 5):
    for s in range(1, 5):
        for H in range(4):
            heads = []
            bias = Q(rng.randrange(-5, 6))
            for h in range(H):
                p = [Q(rng.randrange(1, 5)) for _ in range(r)]
                q = [Q(rng.randrange(1, 5)) for _ in range(s)]
                c = sum(p + q) + Q(rng.randrange(1, 5))
                a0 = Q(rng.randrange(-5, 6))
                a = [Q(rng.randrange(-5, 6)) for _ in range(r)]
                b = [Q(rng.randrange(-5, 6)) for _ in range(s)]
                k = a0 / c
                t = [x + k*y for x, y in zip(a, p)]
                u = [x + k*y for x, y in zip(b, q)]
                eta = min(p + q) / 2
                heads.append((c, p, q, a0, a, b, k, t, u, eta))
            R = [bias + sum(k + t[i]/(c-p[i]-eta)
                 for c,p,q,a0,a,b,k,t,u,eta in heads) for i in range(r)]
            C = [sum(u[j]/(c-eta-q[j])
                 for c,p,q,a0,a,b,k,t,u,eta in heads) for j in range(s)]
            L = Q(2*(r+s)+4)
            scale = (L-2)*(L-3)
            for z in product(range(2), repeat=r):
                for w in product(range(2), repeat=s):
                    dot = lambda a,b: sum(x*y for x,y in zip(a,b))
                    original = bias
                    repaired = Q(0)
                    for c,p,q,a0,a,b,k,t,u,eta in heads:
                        D = c-eta*(sum(z)+sum(w))
                        U = dot(p,z)-eta*sum(z)
                        V = dot(q,w)-eta*sum(w)
                        T, W = dot(t,z), dot(u,w)
                        assert min(D-U-V,D-U,D-V) > 0
                        original += (a0+dot(a,z)+dot(b,w))/(D-U-V)
                        repaired += (T+W)/(D-U-V)-T/(D-U)-W/(D-V)
                    E = L-sum(z)-sum(w)
                    MR,MC = scale*dot(R,z),scale*dot(C,w)
                    assert min(E-sum(w), E-sum(z), E)>0
                    repaired += MR/(E-sum(w))+MC/(E-sum(z))-(MR+MC)/E
                    if sum(z)==0 or sum(w)==0:
                        assert repaired==0
                    if sum(z)==sum(w)==1:
                        assert repaired==original
                    checked += 1
print(f'PASS: {checked} exact cube evaluations; all axes, grids, and denominators verified')
