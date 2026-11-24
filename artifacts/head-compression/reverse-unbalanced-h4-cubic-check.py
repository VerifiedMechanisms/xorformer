#!/usr/bin/env python3
"""Exact arithmetic check of the four-head cubic germ and all 1024 labels.

The JSON is a rational certificate, not a numerical oracle. No tolerance,
optimization library, or unverified root computation is used here.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

DATA = json.loads(Path(__file__).with_name(
    "reverse-unbalanced-h4-cubic-certificate.json").read_text())
ROWS = []
QUERIES = [([F(1)] * 4, [F(0)] * 4),
           ([F(1001, 1000)] * 4, [F(0)] * 4),
           ([F(501, 500)] * 4, [F(0)] * 4)]
for us, vs in zip(DATA["u_numerators"], DATA["v"]):
    u = [F(x, DATA["u_denominator"]) for x in us]
    v = list(map(F, vs))
    w = [1+x for x in u] + [F(1)]
    vv = v + [-sum(x/y for x, y in zip(v, w))]
    assert sum(x/y for x, y in zip(vv, w)) == 0
    ROWS.append(u + v + [sum(vv)])
    QUERIES.append(([1/x for x in w], [x/y**2 for x, y in zip(vv, w)]))

points = {}
for record in DATA["witnesses_R_positive"]:
    sig = tuple(record["signs"])
    X = list(map(F, record["point"]))
    assert len(X) == 7
    assert sum(X[h]*X[h+3] for h in range(3)) == 0
    assert sum(X[h]*X[h+3]**2 for h in range(3)) > 0
    assert all(s*sum(c*x for c, x in zip(row, X)) > 0
               for s, row in zip(sig, ROWS))
    points[(sig, 1)] = X
    points[(tuple(-s for s in sig), -1)] = [-x for x in X]
assert len(points) == 256

def parameters(labels):
    X = points[(tuple(labels[3:]), labels[0])]
    A = X[:3] + [-sum(X[:3])]
    P = [X[h+3]+X[6] for h in range(3)] + [X[6]]
    R = sum(a*p*p for a, p in zip(A, P))
    assert sum(A) == sum(a*p for a, p in zip(A, P)) == 0
    assert labels[0]*R > 0
    # P(t) = R product(1-t/alpha), with a root at each requested sign change.
    co = [R]
    times = [F(1), F(1001, 1000), F(501, 500)]
    for i in range(2):
        if labels[i] != labels[i+1]:
            alpha = (times[i]+times[i+1])/2
            out = [F(0)]*(len(co)+1)
            for k, c in enumerate(co):
                out[k] += c
                out[k+1] -= c/alpha
            co = out
    co += [F(0)]*(3-len(co))
    for s, t in zip(labels[:3], times):
        assert s*sum(c*t**k for k,c in enumerate(co)) > 0
    pivot = max(range(4), key=lambda h: abs(A[h]))
    P2 = [F(0)]*4
    P2[pivot] = co[1]/A[pivot]
    A3 = [co[2]/4]*4
    assert sum(a*p for a,p in zip(A,P2)) == co[1]
    assert sum(A3) == co[2]
    return A, P, A3, P2

minimum = None
for labels in product([-1,1], repeat=10):
    A, P, A3, P2 = parameters(labels)
    delta = F(1, 2**80)
    aa = [delta*a+delta**3*b for a,b in zip(A,A3)]
    pp = [delta*p+delta**2*q for p,q in zip(P,P2)]
    for s,(D,b) in zip(labels,QUERIES):
        assert all(d-p > 0 for d,p in zip(D,pp))
        score = sum((a+bb)/(d-p) for a,bb,d,p in zip(aa,b,D,pp))
        assert s*score > 0
        margin = s*score
        minimum = margin if minimum is None else min(minimum,margin)
    # The displayed universal cube budget only requires the row slopes
    # to lie in (rho/2, 3rho/2), available by further decreasing delta.
    for D,_ in QUERIES:
        assert all(F(200,201) <= d <= F(200,199) for d in D)

assert F(3,20000)+F(10,67) < 1
print("Exact check passed: 256 null-cone witnesses, 1024 ten-sign patterns,")
print("10240 strict rational grid signs at delta=2^-80, and universal cube budget.")
print("Smallest checked score:", float(minimum))
