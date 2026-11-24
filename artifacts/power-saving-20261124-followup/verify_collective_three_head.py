#!/usr/bin/env python3
"""Exact rational cross-check; the relation and pair certificates also have Lean proofs."""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SLOPES = ((2, 3, 3, 3, 3), (2, 1, 2, 2, 2), (1, 3, 2, 2, 2))
NUMERATORS = ((3, 0, 0, 0, 0), (-6, -4, -4, -4, -4), (2, 8, 4, 4, 4))
POINTS = tuple(product((0, 1), repeat=5))


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def row(point, heads):
    return [F(1)] + [F(x, 1 + dot(SLOPES[h], point))
                     for h in heads for x in point]


def rank(matrix):
    matrix = [list(map(F, r)) for r in matrix]
    pivot = 0
    for col in range(len(matrix[0])):
        chosen = next((i for i in range(pivot, len(matrix)) if matrix[i][col]), None)
        if chosen is None:
            continue
        matrix[pivot], matrix[chosen] = matrix[chosen], matrix[pivot]
        scale = matrix[pivot][col]
        matrix[pivot] = [x / scale for x in matrix[pivot]]
        for i in range(len(matrix)):
            if i != pivot and matrix[i][col]:
                scale = matrix[i][col]
                matrix[i] = [a - scale * b for a, b in zip(matrix[i], matrix[pivot])]
        pivot += 1
    return pivot


for point in POINTS:
    denominators = [1 + dot(b, point) for b in SLOPES]
    assert min(denominators) > 0
    assert sum(F(dot(a, point), b) for a, b in zip(NUMERATORS, denominators)) == 0

certificates = json.loads((ROOT / "three_head_pair_certificates.json").read_text())
for pair, certificate in certificates.items():
    heads = tuple(map(int, pair))
    matrix = [row(point, heads) for point in certificate["points"]]
    inverse = [[F(x) for x in r] for r in certificate["inverse"]]
    for i in range(11):
        for j in range(11):
            assert sum(inverse[i][k] * matrix[k][j] for k in range(11)) == (i == j)
    assert rank([row(point, heads) for point in POINTS]) == 11
assert rank([row(point, range(3)) for point in POINTS]) == 15
print("32 exact zero evaluations; 3 invertible pair certificates; pair ranks 11; triple rank 15")
