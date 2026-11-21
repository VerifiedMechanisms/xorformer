#!/usr/bin/env python3
"""Exact rational checks for the probabilistic one-head hinge obstruction.

This verifies finite algebra and constants, not the concentration or calculus
arguments in mechanism-audit.tex. It proves no universal head upper bound.
"""

from fractions import Fraction as Q
import json


def determinant(matrix):
    a = [row[:] for row in matrix]
    result = Q(1)
    for i in range(len(a)):
        pivot = next((j for j in range(i, len(a)) if a[j][i]), None)
        if pivot is None:
            return Q(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            result = -result
        value = a[i][i]
        result *= value
        for j in range(i + 1, len(a)):
            factor = a[j][i] / value
            for k in range(i + 1, len(a)):
                a[j][k] -= factor * a[i][k]
    return result


def gram(rows):
    width = len(rows[0])
    return [[sum(row[i] * row[j] for row in rows) / len(rows)
             for j in range(width)] for i in range(width)]


def main():
    rows, pairs = [], []
    b = [Q(2), Q(3), Q(5)]
    u = [Q(1, 100), Q(7, 100), Q(-4, 100)]
    t_coeff = [Q(1)] + [-v for v in b] + [Q(0)] * 3
    w_coeff = [Q(0)] + [-v for v in u] + [-v for v in b]
    for v in range(8):
        x = [Q((v >> i) & 1) for i in range(3)]
        denominator = 1 + sum(a * z for a, z in zip(b, x))
        numerator = sum(a * z for a, z in zip(u, x))
        row = [Q(1)] + [z / denominator for z in x]
        row += [-numerator * z / denominator**2 for z in x]
        pair = [1 / denominator, -numerator / denominator**2]
        assert sum(a * z for a, z in zip(t_coeff, row)) == pair[0]
        assert sum(a * z for a, z in zip(w_coeff, row)) == pair[1]
        rows.append(row)
        pairs.append(pair)
    base, pair = gram(rows), gram(pairs)
    base_det, pair_det = determinant(base), determinant(pair)
    base_trace = sum(base[i][i] for i in range(7))
    pair_trace = sum(pair[i][i] for i in range(2))
    base_lower = base_det / base_trace**6
    pair_lower = pair_det / pair_trace
    assert base_lower > Q(1, 10**30)
    assert pair_lower > Q(1, 10**6)
    assert sum(v * v for v in t_coeff) <= 39
    assert sum(v * v for v in w_coeff) <= 39

    # Base dimension is n >= 1000; every later inequality only becomes easier.
    n = 1000
    kappa = Q(1, 10**40)
    gamma = Q(1, 10**33 * n)
    delta = kappa / n**6
    radius = delta / 4
    p = 2 * n + 1
    assert Q(1, 40 * 10**30 * n) - 8 * n**2 * delta >= gamma
    assert 6 * p**2 * radius <= gamma / 4
    epsilon = gamma * radius / (8 * p)
    assert epsilon >= Q(1, 10**75 * n**8)
    assert 2**n >= 10**200 * n**20
    assert 2 * n**20 > (n + 1)**20
    assert Q(10**50 * n**4, 2) >= 10 * n**2
    assert 50 * n**4 > 24 * n**2

    print(json.dumps({
        "base_gram_determinant": str(base_det),
        "base_gram_trace": str(base_trace),
        "base_eigenvalue_lower_bound": str(base_lower),
        "pair_gram_determinant": str(pair_det),
        "pair_gram_trace": str(pair_trace),
        "pair_eigenvalue_lower_bound": str(pair_lower),
        "all_finite_checks_passed": True,
        "scope": "Finite rational identities and constants for a one-head "
                 "interior squared-hinge local minimum existence proof. "
                 "Not the requested universal head bound."
    }, indent=2))


if __name__ == "__main__":
    main()
