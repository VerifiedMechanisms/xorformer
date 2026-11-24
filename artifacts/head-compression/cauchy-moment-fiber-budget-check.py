#!/usr/bin/env python3
"""Small exact checks of the mixed Cauchy moment and Hermite matrices.

The general proofs are in cauchy-moment-fiber-budget.tex. These finite
checks are regression tests of the formulas, not a universality proof.
"""
from fractions import Fraction as F


def rank(matrix):
    a = [row[:] for row in matrix]
    r = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        scale = a[r][col]
        a[r] = [x / scale for x in a[r]]
        for i in range(r + 1, len(a)):
            scale = a[i][col]
            a[i] = [x - scale * y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def check(a, p):
    s = 2 * a - p
    nodes = [F(i + 1, 10 * (a + 1)) for i in range(a)]
    weights = [F(i + 1, a + 1) for i in range(a)]
    support = [F(i + 1, 10 * (2 * a + 1)) for i in range(2 * a)]
    times = [1 + F(j + 1, 10 * (2 * a + 1)) for j in range(s)]
    evaluation = []
    jacobian = []
    for k in range(p):
        evaluation.append([x**k for x in support])
        jacobian.append(
            [x**k for x in nodes]
            + [w * k * x ** (k - 1) if k else F(0)
               for w, x in zip(weights, nodes)]
        )
    for t in times:
        evaluation.append([1 / (t - x) for x in support])
        jacobian.append(
            [1 / (t - x) for x in nodes]
            + [w / (t - x)**2 for w, x in zip(weights, nodes)]
        )
    assert rank(evaluation) == 2 * a, (a, p, "evaluation")
    assert rank(jacobian) == 2 * a, (a, p, "Jacobian")


if __name__ == "__main__":
    count = 0
    for atoms in range(1, 7):
        for moments in range(2 * atoms + 1):
            check(atoms, moments)
            count += 1
    print(f"PASS: {count} mixed bases and {count} exact Hermite Jacobians")
