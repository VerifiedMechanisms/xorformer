#!/usr/bin/env python3
"""Exact small checks for the written positive-root construction."""
from fractions import Fraction as F
from itertools import product

def mul_value(t, roots):
    ans = F(1)
    for b in roots:
        ans *= t-b
    return ans

def run():
    words = signs = identities = 0
    for q in range(1,7):
        poles = [F(i+1, 8*q+4) for i in range(2*q)]
        for sigma in product((-1,1), repeat=q):
            roots = [(poles[2*s+1]+poles[2*s+2])/2
                     for s in range(q-1) if sigma[s]!=sigma[s+1]]
            eta = sigma[0] * (1 if mul_value(poles[0],roots)>0 else -1)
            def N(t):
                return eta*(t-F(1,2))*mul_value(t,roots)*mul_value(1-t,roots)
            coeff = []
            for i,p in enumerate(poles):
                qp = mul_value(p,poles[:i]+poles[i+1:])
                u = sigma[i//2]*(1 if i%2==0 else -1)
                c = N(p)/(u*qp)
                assert c>0
                coeff.append(u*c)
            def score(t):
                return sum((c/(t-p) for c,p in zip(coeff,poles)),F(0))
            for s in range(q):
                for x in (poles[2*s],(poles[2*s]+poles[2*s+1])/2,poles[2*s+1]):
                    assert sigma[s]*score(1-x)>0
                    signs += 1
            for t in (F(2),F(3,4),F(-1)):
                assert score(t)*mul_value(t,poles)==N(t)
                assert N(1-t)==-N(t)
                identities += 1
            words += 1
    print(f"PASS: {words} words, {signs} strict query signs, {identities} partial-fraction and antisymmetry checks")

if __name__ == "__main__":
    run()
