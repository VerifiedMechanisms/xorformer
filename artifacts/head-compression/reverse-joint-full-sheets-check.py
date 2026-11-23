#!/usr/bin/env python3
"""Exact finite checks for full regular reciprocal permutation sheets."""
from fractions import Fraction as Q
from itertools import permutations, product


def determinant(matrix):
    a = [list(row) for row in matrix]
    n = len(a)
    ans = Q(1)
    for k in range(n):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return Q(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            ans = -ans
        value = a[k][k]
        ans *= value
        for j in range(k, n):
            a[k][j] /= value
        for i in range(k + 1, n):
            value = a[i][k]
            for j in range(k, n):
                a[i][j] -= value * a[k][j]
    return ans


count = 0
for h in range(1, 5):
    epsilon = Q(1, 100)
    lam = [epsilon * Q(j + 1, h + 1) for j in range(h)]
    mu = [Q((j + 1) ** 2 - 3) for j in range(h)]
    d = [1 - epsilon * Q(i + 1, h + 1) for i in range(h)]
    c = [[1 / (di - lj) for lj in lam] for di in d]
    square = [[x * x for x in row] for row in c]
    expected = (-1) ** h * determinant(c) * determinant(square)
    assert expected
    r = [sum(mu[j] * c[i][j] for j in range(h)) for i in range(h)]
    s = [sum(c[i]) for i in range(h)]
    for perm in permutations(range(h)):
        u = [lam[j] for j in perm]
        a = [mu[j] for j in perm]
        jacobian = []
        for t in (0, 1):
            for i, di in enumerate(d):
                value = sum((t + a[j]) / (di - u[j]) for j in range(h))
                assert value == r[i] + t * s[i]
                jacobian.append(
                    [(t + a[j]) / (di - u[j]) ** 2 for j in range(h)]
                    + [1 / (di - u[j]) for j in range(h)]
                )
        assert determinant(jacobian) == expected
        count += 1

# H=2, s=2: every Boolean vertex, independently chosen compact columns.
h, s = 2, 2
epsilon = Q(1, 100)
d = [1 - Q(i + 1, 3) * epsilon for i in range(h)]
u = [[epsilon * Q(1 + k + j, 5) for j in range(s)] for k in range(h)]
eta = Q(1, 100)
for bits in product((0, 1), repeat=2 * h + s):
    z, w = bits[: 2 * h], bits[2 * h :]
    for k in range(h):
        b = 1 - sum((1 - d[i]) * (z[2 * i] + z[2 * i + 1]) for i in range(h))
        b -= sum(u[k][j] * w[j] for j in range(s))
        assert b > Q(3, 4)
    assert 1 - eta * sum(bits) > Q(1, 2)

print(f"PASS: {count} exact sheet/Jacobian checks; 64 full-cube vertices.")
