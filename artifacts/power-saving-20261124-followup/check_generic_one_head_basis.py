#!/usr/bin/env python3
"""Exact integer and Fraction checks for the two open one-head branches."""
from fractions import Fraction
import itertools
import json

X = [(1,) + x for x in itertools.product((0, 1), repeat=7)]
I = [98, 117, 50, 30, 123, 124, 119, 67]
G = [-1, -1, 1, -1, -1, 1, 1, 1]
T = [
    [-7, -6, -6, -6, -2, -6, -4, -4],
    [16, 13, 12, 12, 6, 10, 10, 8],
    [-12, -10, -9, -8, -4, -6, -8, -6],
    [18, 14, 14, 13, 6, 10, 12, 8],
    [-8, -6, -6, -6, -3, -4, -6, -4],
    [-6, -4, -4, -4, -2, -3, -4, -2],
    [2, 2, 2, 2, 0, 2, 1, 2],
    [-10, -8, -8, -8, -4, -6, -6, -5],
]
B = [[1, 1, 1, 1, 1, 1, 4, 1], [1, 1, 1, 1, 1, 3, 1, 1]]
A = [[-53, 117, -87, 131, -61, -41, 16, -73],
     [-53, 107, -75, 115, -51, -35, 17, -67]]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def determinant(mat):
    a = [[Fraction(v) for v in row] for row in mat]
    ans = Fraction(1)
    for k in range(len(a)):
        pivot = next(j for j in range(k, len(a)) if a[j][k])
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            ans = -ans
        d = a[k][k]
        ans *= d
        for j in range(k + 1, len(a)):
            q = a[j][k] / d
            a[j] = [u - q * v for u, v in zip(a[j], a[k])]
    return ans


M = [[sum(x[j] * T[j][k] for j in range(8)) for k in range(8)] for x in X]
assert determinant([X[i] for i in I]) == -1
assert all(M[i] == [g * v for v in X[i]] for i, g in zip(I, G))
structural = [i for i in range(128) if M[i] == list(X[i]) or M[i] == [-v for v in X[i]]]
assert structural == [30, 50, 67, 72, 98, 117, 119, 123, 124]
labels = []
records = []
for k in range(2):
    assert all(v > 0 for v in B[k])
    assert [dot(t, B[k]) for t in T] == A[k]
    numerator = [dot(x, A[k]) for x in X]
    denominator = [dot(x, B[k]) for x in X]
    signed = [abs(a) - b for a, b in zip(numerator, denominator)]
    assert all(v >= 0 for v in signed)
    assert min(signed[i] for i in range(128) if i not in structural) == 2
    assert all(Fraction(numerator[i], denominator[i]) == g for i, g in zip(I, G))
    labels.append([a > 0 for a in numerator])
    records.append({'minimum_nonstructural_residual': 2,
                    'structural_rows': structural,
                    'basis_values': G,
                    'denominator': B[k], 'numerator': A[k]})
disagreement = [i for i in range(128) if labels[0][i] != labels[1][i]]
assert disagreement == [17]
print(json.dumps({'dimension': 7, 'heads': 1, 'basis': I,
                  'affine_basis_determinant': -1,
                  'disagreement': disagreement, 'branches': records}, indent=2))
