#!/usr/bin/env python3
"""Exact leading Pluecker coefficients of compact reciprocal kernels.

This checks the first three weighted-moment layers, not an asymptotic
shattering theorem.  All arithmetic is integral.
"""
from itertools import combinations, permutations
from math import comb


def determinant(matrix):
    n = len(matrix)
    total = 0
    for p in permutations(range(n)):
        sign = (-1)**sum(p[i] > p[j] for i in range(n) for j in range(i+1, n))
        product = sign
        for i in range(n):
            product *= matrix[i][p[i]]
        total += product
    return total


def determinant_series(linear_forms, degree):
    """det(1/(1-eps*L_ih)) modulo eps**(degree+1)."""
    n = len(linear_forms)
    powers = [[[x**k for k in range(degree+1)] for x in row]
              for row in linear_forms]
    dp = {0: [1]+[0]*degree}
    for size in range(n):
        next_dp = {}
        for mask, coefficients in dp.items():
            for h in range(n):
                if mask & (1 << h):
                    continue
                sign = (-1)**sum(bool(mask & (1 << k)) for k in range(h+1, n))
                target = next_dp.setdefault(mask | (1 << h), [0]*(degree+1))
                for k, x in enumerate(coefficients):
                    if x:
                        for ell in range(degree+1-k):
                            target[k+ell] += sign*x*powers[size][h][ell]
        dp = next_dp
    return dp[(1 << n)-1]


checked = 0
nonzero = 0
for n, base, boundary, valuation in (
    (3, [(0, 0), (1, 0)], [(2, 0), (0, 1)], 3),
    (4, [(0, 0), (1, 0), (2, 0), (0, 1)], [], 5),
    (5, [(0, 0), (1, 0), (2, 0), (0, 1)], [(3, 0), (1, 1)], 8),
):
    c = list(range(n))
    rows = [(i, ((i+2)*(i+3)) % 11-5) for i in range(n+1)]
    tested_permutations = list(permutations(range(1, n+1)))[:min(12, 2*n)]
    for lam in tested_permutations:
        for row_indices in combinations(range(n+1), n):
            chosen_rows = [rows[i] for i in row_indices]
            linear_forms = [[v0+c[h]*v+lam[h] for h in range(n)]
                            for v, v0 in chosen_rows]
            actual = determinant_series(linear_forms, valuation)
            assert all(x == 0 for x in actual[:valuation])
            predicted = 0
            choices = [base+[moment] for moment in boundary] if boundary else [base]
            for moments in choices:
                parameter = [[c[h]**a*lam[h]**b for h in range(n)]
                             for a, b in moments]
                evaluation = [[comb(a+b, a)*v**a*v0**b for a, b in moments]
                              for v, v0 in chosen_rows]
                predicted += determinant(parameter)*determinant(evaluation)
            assert actual[valuation] == predicted, (n, lam, row_indices, actual, predicted)
            checked += 1
            nonzero += actual[valuation] != 0

print(f"Verified {checked} leading Pluecker coefficients through H=5; {nonzero} nonzero coefficients.")
print("Second-order graph coefficient is (a dot lambda), not 2*(a dot lambda).")
