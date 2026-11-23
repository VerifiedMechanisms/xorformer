#!/usr/bin/env python3
"""Exact checks for deformed reciprocal sheets; no shattering claim."""
from fractions import Fraction as F
from itertools import permutations
from math import prod


def transpose(a):
    return list(map(list, zip(*a)))


def multiply(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in transpose(b)]
            for row in a]


def inverse(a):
    n = len(a)
    m = [list(row) + [F(i == j) for j in range(n)] for i, row in enumerate(a)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if m[i][j])
        m[j], m[pivot] = m[pivot], m[j]
        scale = m[j][j]
        m[j] = [x/scale for x in m[j]]
        for i in range(n):
            if i != j:
                scale = m[i][j]
                m[i] = [x-scale*y for x, y in zip(m[i], m[j])]
    return [row[n:] for row in m]


def determinant(a):
    n = len(a)
    m = [list(row) for row in a]
    out = F(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if m[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            m[j], m[pivot] = m[pivot], m[j]
            out = -out
        scale = m[j][j]
        out *= scale
        for i in range(j+1, n):
            factor = m[i][j]/scale
            m[i] = [x-factor*y for x, y in zip(m[i], m[j])]
    return out


checked = 0
for n in range(1, 5):
    lam = [F(j+1, 100*(n+1)) for j in range(n)]
    d = [1-F(i+1, 100*(n+1)) for i in range(n)]
    c = [[1/(x-y) for y in lam] for x in d]
    c2 = [[x*x for x in row] for row in c]
    u = [[F((i+2)*(j+3) % 7 - 3) for j in range(n)] for i in range(n)]
    e_matrix = multiply(c, u)
    inv_c = inverse(c)
    for p in permutations(range(n)):
        inv_p = [p.index(j) for j in range(n)]
        cp = [[row[p[h]] for h in range(n)] for row in c]
        ep = [sum(e_matrix[i][h]*cp[i][h] for h in range(n)) for i in range(n)]
        a = [-x[0] for x in multiply(inverse(cp), [[x] for x in ep])]
        residual = [[e_matrix[i][h]+a[h] for h in range(n)] for i in range(n)]
        for i in range(n):
            assert sum(residual[i][h]*cp[i][h] for h in range(n)) == 0
            assert sum((residual[i][h]+1)*cp[i][h] for h in range(n)) == sum(c[i])
        jacobian = [
            [residual[i][h]*cp[i][h]**2 for h in range(n)] + cp[i]
            for i in range(n)
        ] + [[cp[i][h]**2 for h in range(n)] + [F(0)]*n for i in range(n)]
        assert determinant(jacobian) == (-1)**n * determinant(c) * determinant(c2)
        assert determinant(jacobian) != 0

        # Coefficient of eta in the cleared readout numerator. Since its
        # constant term is zero, dividing by the denominator at eta=0
        # gives the exact derivative without any finite-difference test.
        v = [F(2*h+1-n) for h in range(n)]
        for i in range(n):
            den = [d[i]-lam[p[h]] for h in range(n)]
            coefficient = sum(
                residual[i][h] * sum(
                    v[k]*prod(den[l] for l in range(n) if l != h and l != k)
                    for k in range(n) if k != h
                ) for h in range(n)
            )
            derivative = -sum(v[h]*residual[i][h]/den[h]**2 for h in range(n))
            assert coefficient/prod(den) == derivative

        t = [u[k][inv_p[k]] for k in range(n)]
        b = [
            sum(u[j][h]/(lam[j]-lam[p[h]]) for h in range(n) if p[h] != j)
            - sum(u[l][inv_p[j]]/(lam[l]-lam[j]) for l in range(n) if l != j)
            for j in range(n)
        ]
        reconstructed_e = [
            sum(c[i][j]*b[j] + c2[i][j]*t[j] for j in range(n))
            for i in range(n)
        ]
        assert ep == reconstructed_e
        mt = multiply(multiply(inv_c, c2), [[x] for x in t])
        assert a == [-b[p[h]]-mt[p[h]][0] for h in range(n)]
        checked += 1

print(f"Verified {checked} exact sheets, full Jacobians, derivative identities, and preconditioning formulas.")
