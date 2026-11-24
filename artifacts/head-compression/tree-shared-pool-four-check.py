#!/usr/bin/env python3
"""Exact finite certificate for the shared four-term Cauchy pool.

This checks all rational limiting inequalities and all 16 internal patterns
for each of 16 root patterns at one explicit positive epsilon.  The
companion TeX proof establishes persistence for every sufficiently small
epsilon and the eight-term, twenty-query consequence.
"""
from fractions import Fraction as F
from itertools import permutations
from functools import reduce
import json

ETA = F(1, 1000)
EPS = F(1, 100000)
ROOT_OFFSETS = [
    [-34, -1, 44], [17, -15, -12], [-7, -24, 45],
    [26, -27, -2], [-52, 23, 14], [43, -36, -16],
    [-42, 19, 6], [33, 12, -27],
]
A = [-3, -1, 1, 3]
B = [0, 16, 0, 0]
V = [F(-1, 48), F(3, 48), F(-3, 48), F(1, 48)]
L = [sum(F(B[i]-B[j], A[i]-A[j]) for j in range(4) if i != j)
     for i in range(4)]
assert L == [8, -4, -8, -4]
assert sum(A[i]*V[i] for i in [0, 3]) == F(1, 8)
assert sum(V[i]*L[i] for i in [0, 3]) == F(-1, 4)
assert sum(V[i]*L[i] for i in [1, 2]) == F(1, 4)

q = [EPS*A[i] + EPS*EPS*B[i] for i in range(4)]
p = [4*EPS+x for x in q]
times = [1+ETA*u for u in [-3, -1, 1, 3]]
child_times = [1-2*ETA, 1+2*ETA]


def sign_pattern(values):
    assert all(values)
    return sum((x > 0) << i for i, x in enumerate(values))


coverage = {}
for offsets in ROOT_OFFSETS:
    roots = [1+ETA*F(v, 10) for v in offsets]
    def numerator(t):
        return reduce(lambda a, b: a*b, [t-r for r in roots], F(1))
    zero = 1/(sum(1/r for r in roots)-2)
    assert child_times[0] < zero < child_times[1]
    base = [numerator(q[i])/reduce(lambda a, b: a*b,
            [q[i]-q[j] for j in range(4) if i != j], F(1))
            for i in range(4)]
    for orientation in [1, -1]:
        residues = [orientation*x for x in base]
        root_pattern = sign_pattern([sum(residues[i]/(t-q[i])
                                        for i in range(4)) for t in times])
        assert root_pattern == sign_pattern([orientation*numerator(t) for t in times])
        witnesses = {}
        for pi in permutations(range(4)):
            values = [sum(residues[pi[i]]/(t-q[pi[i]]) for i in [1, 3])
                      for t in child_times]
            values += [residues[pi[2]], residues[pi[3]]]
            witnesses[sign_pattern(values)] = pi
        assert set(witnesses) == set(range(16))
        coverage[root_pattern] = {'offsets_tenths': offsets,
                                  'orientation': orientation,
                                  'limiting_pair_zero': str(zero),
                                  'internal_patterns': len(witnesses)}
assert set(coverage) == set(range(16))
print(json.dumps({'root_patterns': len(coverage),
                  'internal_patterns_per_pool': 16,
                  'epsilon': str(EPS),
                  'coverage': coverage}, indent=2, sort_keys=True))
