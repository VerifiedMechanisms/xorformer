#!/usr/bin/env python3
"""Finite exact checks for deletion-star-denominator-budget.md."""
from fractions import Fraction as F
from itertools import product, permutations
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
counts = {"extension_tables": 0, "sample_equalities": 0,
          "gauge_checks": 0, "matching_checks": 0}
for r, m in ((2, 2), (2, 3), (3, 2), (3, 3)):
    for values in product((F(1), F(2), F(4)), repeat=r + m):
        theta, poles = values[:r], values[r:]
        gap = sum(values) - (r-1)*max(theta) - (m-1)*max(poles)
        for shift in (F(-5, 3), F(7, 2)):
            shifted_t = tuple(t+shift for t in theta)
            shifted_p = tuple(p-shift for p in poles)
            assert (sum(shifted_t)+sum(shifted_p)
                    -(r-1)*max(shifted_t)-(m-1)*max(shifted_p)) == gap
            counts["gauge_checks"] += 1
        if gap <= 0:
            continue
        eta = gap / (4*(r-1))
        xi = gap / (4*(m-1))
        alpha, beta = max(theta)+eta, max(poles)+xi
        slopes = tuple(alpha-t for t in theta) + tuple(beta-p for p in poles)
        constant = sum(values)-(r-1)*alpha-(m-1)*beta
        assert constant > 0 and min(slopes) > 0
        center = constant+sum(slopes)
        assert center == alpha+beta
        for i in range(r):
            for j in range(m):
                assert center-slopes[i]-slopes[r+j] == theta[i]+poles[j]
                counts["sample_equalities"] += 1
        counts["extension_tables"] += 1

assert 2*100+2*1 == 202
assert 1+100+1+1+1+1 == 105

for weights in product((F(1), F(2), F(5)), repeat=6):
    center = F(1)+sum(weights)
    for tau in (F(1, 4), F(1, 2), F(2, 3), F(3, 4), F(9, 10)):
        edges = {(i,j) for i in range(3) for j in range(3)
                 if center-weights[i]-weights[3+j] <= tau*center}
        maximum = 0
        for k in range(1,4):
            if any(all((i,j) in edges for i,j in zip(rows,cols))
                   for rows in permutations(range(3),k)
                   for cols in permutations(range(3),k)):
                maximum = k
        assert maximum*(1-tau) < 1
        if tau <= F(1,2) and edges:
            assert (any(all(i==v for i,j in edges) for v in range(3)) or
                    any(all(j==v for i,j in edges) for v in range(3)))
        counts["matching_checks"] += 1

files = (root/"deletion-star-denominator-budget.md", Path(__file__).resolve())
result = {"status": "PASS", "scope": "finite exact rational checks, not Lean",
          "counts": counts,
          "sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
(root/"deletion-star-denominator-budget-audit.json").write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
