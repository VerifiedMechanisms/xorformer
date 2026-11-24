#!/usr/bin/env python3
"""Exact finite check of the generic compact-permutation stability audit."""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import factorial, comb


def det(a):
    a = [list(row) for row in a]
    out = F(1)
    for j in range(len(a)):
        k = next((k for k in range(j, len(a)) if a[k][j]), None)
        if k is None:
            return F(0)
        if k != j:
            a[k], a[j] = a[j], a[k]
            out = -out
        pivot = a[j][j]
        out *= pivot
        for k in range(j + 1, len(a)):
            factor = a[k][j] / pivot
            for l in range(j + 1, len(a)):
                a[k][l] -= factor * a[j][l]
    return out


H, q = 3, 10
d = H + 1
p = tuple(range(1, H + 1))
P = max(p)
delta = F(1, (q + 1) ** (H * (H + 1) // 2))
epsilon = delta / (32 * P * factorial(d) * d * 3 ** (d - 1))
D = [[1 / (1 + F(j, q + 1) ** h) for h in range(1, H + 1)]
     for j in range(1, q + 1)]
base = [[F(1)] + [1 / x for x in row] for row in D]
supports = list(combinations(range(q), d))
baseline = [det([base[j] for j in I]) for I in supports]
assert all(x >= delta for x in baseline)
checked = 0
for pi in permutations(p):
    M = [[F(1)] + [1 / (row[h] - epsilon * pi[h]) for h in range(H)]
         for row in D]
    assert all(row[h] > epsilon * pi[h] for row in D for h in range(H))
    for I, before in zip(supports, baseline):
        after = det([M[j] for j in I])
        assert after * before > 0
        assert abs(after - before) < delta / 2
        checked += 1

print({"heads": H, "queries": q, "permutations": factorial(H),
       "exact_minor_checks": checked,
       "strict_sign_vectors_per_sheet": 2 * sum(comb(q - 1, k) for k in range(d)),
       "all_possible_sign_vectors": 2 ** q,
       "epsilon": str(epsilon)})
