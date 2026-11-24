#!/usr/bin/env python3
"""Exact finite checks for the common-pool adaptive-bias obstruction.

The .tex proof, not this test, establishes the theorem for all inputs.
No numerical LP solver or tolerance is used here.
"""
from fractions import Fraction as Q
from itertools import product
import json
import random


def rank(matrix):
    a = [list(row) for row in matrix]
    pivot = 0
    for col in range(len(a[0])):
        row = next((r for r in range(pivot, len(a)) if a[r][col]), None)
        if row is None:
            continue
        a[pivot], a[row] = a[row], a[pivot]
        v = a[pivot][col]
        a[pivot] = [x / v for x in a[pivot]]
        for r in range(pivot + 1, len(a)):
            if a[r][col]:
                v = a[r][col]
                a[r] = [x - v * y for x, y in zip(a[r], a[pivot])]
        pivot += 1
        if pivot == len(a):
            break
    return pivot


def polynomial_num(u, v, poles, residues):
    total = Q(0)
    for i, r in enumerate(residues):
        z = r
        for j, p in enumerate(poles):
            if i != j:
                z *= (u - p) * (v - p)
        total += z
    return total


def denominator(u, v, poles):
    result = Q(1)
    for p in poles:
        result *= (u - p) * (v - p)
    return result


def simple(t, poles, residues):
    return sum((r / (t - p) for p, r in zip(poles, residues)), Q(0))


rng = random.Random(20261124)
columns = [([Q(rng.randrange(21), 1000) for _ in range(4)],
            [Q(rng.randrange(-10, 11)) for _ in range(4)])
           for _ in range(14)]
queries = [(Q(100 + i, 100), Q(150 + rng.randrange(100), 100)) for i in range(16)]
mat = []
identity_checks = 0
symmetry_checks = 0
for u, v in queries:
    row = []
    for poles, residues in columns:
        p = polynomial_num(u, v, poles, residues)
        d = denominator(u, v, poles)
        assert (simple(u, poles, residues) - simple(v, poles, residues)) == (v-u)*p/d
        assert p == polynomial_num(v, u, poles, residues)
        row.append(p)
        identity_checks += 1
        symmetry_checks += 1
    mat.append(row)
actual_rank = rank(mat)
assert actual_rank <= 10

# Check the exact equivalence used after bias cancellation. For each row,
# all independent signs satisfy eps_i*(C eps)_i>0 exactly when the row
# has positive diagonal and strict absolute off-diagonal dominance.
dominance_cases = 0
for m in range(1, 6):
    for trial in range(30):
        c = [[Q(rng.randrange(-8, 9)) for _ in range(m)] for _ in range(m)]
        if trial % 2:
            for i in range(m):
                c[i][i] = 1 + sum(abs(c[i][j]) for j in range(m) if j != i)
        for i in range(m):
            all_signs = all(e[i] * sum(c[i][j]*e[j] for j in range(m)) > 0
                            for e in product((-1, 1), repeat=m))
            dominant = c[i][i] > sum(abs(c[i][j]) for j in range(m) if j != i)
            assert all_signs == dominant
            dominance_cases += 1

result = {
    "status": "exact finite checks passed; universal theorem is the written proof",
    "divided_difference_identities": identity_checks,
    "symmetric_numerator_checks": symmetry_checks,
    "numerator_evaluation_matrix_shape": [len(mat), len(mat[0])],
    "numerator_evaluation_matrix_rank": actual_rank,
    "sign_dominance_equivalence_cases": dominance_cases,
}
print(json.dumps(result, indent=2))
