#!/usr/bin/env python3
"""Exact checks for geometric-cauchy-slot-audit.tex; no external packages."""
from fractions import Fraction as F
from itertools import combinations, product


def ratio(matrix, i, j):
    return matrix[i][j] * matrix[j][i] / (matrix[i][i] * matrix[j][j])


budgets = 0
for coordinates in product(range(4), repeat=6):
    if sum(coordinates) >= 8:
        continue
    p, q = coordinates[:3], coordinates[3:]
    kernel = [[F(1, 8 - p[i] - q[j]) for j in range(3)] for i in range(3)]
    small = [i for i in range(3) if 2 * (p[i] + q[i]) < 8]
    assert len(small) >= 2
    assert any(ratio(kernel, i, j) > F(1, 4) for i, j in combinations(small, 2))
    budgets += 1

crossratios = 0
for separation in (16, 17, 32, 256):
    a = [F(separation) ** i for i in range(4)]
    kernel = [[1 / (x + y) for y in a] for x in a]
    row = [F(2), F(-3), F(5), F(-7)]
    col = [F(11), F(13), F(-17), F(19)]
    scaled = [[row[i] * col[j] * kernel[i][j] for j in range(4)] for i in range(4)]
    # phi(x) = (2x+3)/(x+1), with token u=-a and query v=a.
    # Shift geometric scales to avoid the pole u=-1.
    aa = [2 * x for x in a]
    phi = lambda x: (2 * x + 3) / (x + 1)
    transformed = [[1 / (phi(y) - phi(-x)) for y in aa] for x in aa]
    original = [[1 / (x + y) for y in aa] for x in aa]
    for i, j in combinations(range(4), 2):
        assert ratio(kernel, i, j) < F(1, 4)
        assert ratio(scaled, i, j) == ratio(kernel, i, j)
        assert ratio(transformed, i, j) == ratio(original, i, j)
        crossratios += 1

robust = 0
for loss in (F(1), F(3, 2), F(2), F(5)):
    r = 16 * loss**4
    assert 4 * r / (1 + r)**2 * loss**4 < F(1, 4)
    robust += 1

localization = 0
for size in range(1, 17):
    for base in (6, 8, 16):
        a = [base ** (2 * i) for i in range(size)]
        matrix = [[F(base ** (i + j), a[i] + a[j]) for j in range(size)] for i in range(size)]
        for i in range(size):
            assert matrix[i][i] == F(1, 2)
            assert sum(matrix[i][j] for j in range(size) if j != i) < F(1, 2)
            localization += 1
        if size <= 8:
            for word in product((-1, 1), repeat=size):
                assert all(word[i] * sum(matrix[i][j] * word[j] for j in range(size)) > 0
                           for i in range(size))

print(f"PASS: {budgets} budget matrices, {crossratios} cross-ratio/projective checks, "
      f"{robust} robust bounds, {localization} localized rows; all sign words through size 8")
