"""Finite exact audits of the CRT pole-matching construction.

The proof in pole-matching-fibers.md works for arbitrary H and k. This script
checks concrete CRT instances, distinct full-cube evaluations, equal sampled
data, and invertibility of the confluent Cauchy blocks. It is not a sign
complexity lower-bound test.
"""

import argparse
from fractions import Fraction as Q
from itertools import permutations, product
import json
from math import factorial, isqrt, prod
from verify_integer_fiber import determinant


def primes_above_three(count):
    out, p = [], 5
    while len(out) < count:
        if all(p % d for d in range(2, isqrt(p)+1)):
            out.append(p)
        p += 1
    return out


def construct(h, k):
    triples = [(j,r,s) for j in range(1,k) for r in range(h) for s in range(h)]
    primes = dict(zip(triples, primes_above_three(len(triples))))
    modulus = prod(p*p for p in primes.values())
    values = [[0]*k for _ in range(h)]
    for (j,r,s), p in primes.items():
        m = p*p
        multiplier = (modulus//m)*pow(modulus//m,-1,m)
        for a in range(h):
            for c in range(k):
                residue = (0 if a==r else 1) if c==0 else (
                    (p-1 if a==s else 1) if c==j else 1)
                values[a][c] += residue*multiplier
    return [[modulus+v%modulus for v in row] for row in values], primes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--heads',type=int,default=3)
    ap.add_argument('--selectors',type=int,default=3)
    args = ap.parse_args()
    h,k=args.heads,args.selectors
    assert h>=2 and k>=2
    b,primes=construct(h,k)
    assert all(a>0 for row in b for a in row)
    for (j,r,s),p in primes.items():
        for a in range(h):
            for c in range(h):
                den=1+b[a][0]+b[c][j]
                if (a,c)==(r,s):
                    assert den%(p*p)==p
                else:
                    assert den%p
    for j in range(k):
        assert len({row[j] for row in b})==h
        jac=[[Q(1,t+b[a][j]) for a in range(h)]+
             [-Q(1,(t+b[a][j])**2) for a in range(h)] for t in range(1,2*h+1)]
        assert determinant(jac)
    perms=list(permutations(range(h)))
    signatures=set()
    common=[[sum(Q(1,t+b[a][j]) for a in range(h)) for t in range(1,2*h+1)]
            for j in range(k)]
    for tail in product(perms,repeat=k-1):
        pi=[tuple(range(h))]+list(tail)
        for j in range(k):
            for t in range(1,2*h+1):
                assert sum(Q(1,t+b[pi[j][a]][j]) for a in range(h))==common[j][t-1]
        signature=tuple(sum(Q(2,1+b[a][0]+b[pi[j][a]][j]) for a in range(h))
                        for j in range(1,k))
        assert signature not in signatures
        signatures.add(signature)
    count=factorial(h)**(k-1)
    assert len(signatures)==count
    print(json.dumps({'status':'VERIFIED','heads':h,'selectors':k,
                      'distinct_regular_branches':count,'sample_size':2*h*k,
                      'maximum_slope_bits':max(v.bit_length() for row in b for v in row),
                      'boolean_sign_patterns_in_this_family':1},indent=2))


if __name__=='__main__':
    main()
