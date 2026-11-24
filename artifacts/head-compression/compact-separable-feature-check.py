#!/usr/bin/env python3
"""Exact arithmetic checks for compact-separable-feature-bound.tex."""
from fractions import Fraction as Q
from itertools import combinations
import json
from pathlib import Path


def product(xs):
    value = Q(1)
    for x in xs:
        value *= x
    return value


def subsets(items):
    for k in range(len(items) + 1):
        yield from combinations(items, k)


checks = []
for H in range(1, 8):
    universe = tuple(range(H))
    for seed in range(1, 5):
        p = [Q((h + 1) * seed, 100 * H * H) for h in universe]
        a = [Q((-1) ** h * (h + seed), h + 2) for h in universe]
        D = [Q(1) + Q((h + seed) ** 2, 10 * H * H) for h in universe]
        b = [Q((-1) ** (h + seed) * (2 * h + seed), h + 3) for h in universe]
        assert all(D[h] > p[h] for h in universe)
        direct = sum((a[h] + b[h]) * product(D[k] - p[k] for k in universe if k != h)
                     for h in universe)
        expanded = Q(0)
        for S0 in subsets(universe):
            S = set(S0)
            if S:
                AS = sum(a[h] * product(p[k] for k in S if k != h) for h in S)
                expanded += (-1) ** (len(S) - 1) * AS * product(D[k] for k in universe if k not in S)
            if len(S) < H:
                expanded += (-1) ** len(S) * product(p[k] for k in S) * sum(
                    b[h] * product(D[k] for k in universe if k not in S and k != h)
                    for h in universe if h not in S)
        assert direct == expanded
        if H == 2:
            z = a[0] * p[1] + a[1] * p[0]
            specialized = (-z + D[1] * a[0] + D[0] * a[1]
                           - b[1] * p[0] - b[0] * p[1]
                           + b[0] * D[1] + b[1] * D[0])
            assert specialized == direct
        checks.append({"heads": H, "seed": seed, "feature_dimension": 2 ** (H + 1) - 3})

out = {"status": "all exact rational identities passed", "checks": checks,
       "two_head_maximum_shattered_queries": 5,
       "six_affine_hyperplanes_in_R5_region_bound": 63,
       "verification_scope": "written theorem plus exact rational tests, not Lean"}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({"checks": len(checks), "status": out["status"]}))
