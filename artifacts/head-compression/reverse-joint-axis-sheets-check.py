#!/usr/bin/env python3
"""Exact checks for the strict axis-zero reciprocal-sheet compiler.

The inverse function theorem is used in the written proof, not replaced
by finite enumeration. All computations below use rational arithmetic.
"""
from fractions import Fraction as Q
from itertools import permutations, product
from math import prod


def det(matrix):
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


def sheet_data(k, s):
    r = 3 * k - 1
    eps = Q(1, 100 * (r + s + 1))
    p = 1 - 2 * eps
    lam = [Q(j + 1, k + 1) * eps for j in range(k)]
    kap = [lam[i] for t in (0, 1) for i in range(k)] + [eps / 2] * (k - 1)
    d = [p - lam[i] for i in range(k)]
    const = [Q(0)] * k
    const += [-sum(1 / (di - lj) - 1 / di for lj in lam) for di in d]
    const += [Q(0)] * (k - 1)
    T = []
    for h in range(k):
        T.append([Q(t) for t in (0, 1) for i in range(k)]
                 + [Q((h == ell) - (h == ell + 1)) for ell in range(k - 1)])
    return r, eps, p, lam, kap, d, const, T


sheets = 0
for k in range(1, 5):
    r, eps, p, lam, kap, d, const, T = sheet_data(k, 2)
    C = [[1 / (di - lj) for lj in lam] for di in d]
    K = [[1 / (di - lj) - 1 / (p - lj) for lj in lam] for di in d]
    E = [[x * x for x in row] for row in C]
    expected = (-1) ** k * det(K) * det(E)
    assert expected
    assert det(K) == det(C) * prod(p - di for di in d) / prod(p - lj for lj in lam)
    for perm in permutations(range(k)):
        u = [lam[j] for j in perm]
        jac = []
        for t in (0, 1):
            for i, di in enumerate(d):
                assert sum(t / (di - uh) - t / di for uh in u) + const[t * k + i] == 0
                jac.append([t / (di - uh) ** 2 for uh in u]
                           + [1 / (di - uh) - 1 / (p - uh) for uh in u])
        assert det(jac) == expected
        sheets += 1

orientations = 0
for k in range(1, 7):
    for signs in product((-1, 1), repeat=k - 1):
        # An arrow points from the smaller required value to the larger.
        outgoing = [set() for _ in range(k)]
        incoming = [0] * k
        for ell, sign in enumerate(signs):
            small, large = (ell + 1, ell) if sign > 0 else (ell, ell + 1)
            outgoing[small].add(large)
            incoming[large] += 1
        order = []
        available = [h for h in range(k) if incoming[h] == 0]
        while available:
            h = available.pop()
            order.append(h)
            for other in outgoing[h]:
                incoming[other] -= 1
                if incoming[other] == 0:
                    available.append(other)
        assert len(order) == k
        rank = [None] * k
        for value, h in enumerate(order):
            rank[h] = value
        assert all(sign * (rank[ell] - rank[ell + 1]) > 0 for ell, sign in enumerate(signs))
        orientations += 1

# Full-cube formula with nonzero residues, including both exact axes.
k, s = 2, 2
r, eps, p, lam, kap, d, const, T = sheet_data(k, s)
u = [[eps / 4, 3 * eps / 4], [2 * eps / 3, eps / 3]]
a = [[Q(2), Q(-3)], [Q(-1), Q(4)]]
bias_scale = 1 / (p - eps) - 1 / p


def cube_score(z, w):
    D = 1 - eps * (sum(z) + sum(w))
    U = sum(kap[i] * z[i] for i in range(r))
    V = [sum(u[h][j] * w[j] for j in range(s)) for h in range(k)]
    A = [sum(a[h][j] * w[j] for j in range(s)) for h in range(k)]
    Tr = [sum(T[h][i] * z[i] for i in range(r)) for h in range(k)]
    L = sum(const[i] * z[i] for i in range(r)) / bias_scale
    denoms = [D - U - Vh for Vh in V] + [D - U] + [D - Vh for Vh in V] + [D - eps * sum(w), D]
    assert len(denoms) == 2 * k + 3
    assert all(den > 1 - 2 * (r + s) * eps for den in denoms)
    score = sum((Tr[h] + A[h]) / (D - U - V[h]) for h in range(k))
    score -= sum(Tr) / (D - U)
    score -= sum(A[h] / (D - V[h]) for h in range(k))
    score += L / (D - eps * sum(w)) - L / D
    return score


vertices = 0
for bits in product((0, 1), repeat=r + s):
    z, w = bits[:r], bits[r:]
    score = cube_score(z, w)
    if not any(z) or not any(w):
        assert score == 0
    vertices += 1
for i in range(r):
    z = [int(ell == i) for ell in range(r)]
    for j in range(s):
        w = [int(ell == j) for ell in range(s)]
        di = p - kap[i]
        query = sum((T[h][i] + a[h][j]) / (di - u[h][j])
                    - T[h][i] / di - a[h][j] / (p - u[h][j]) for h in range(k)) + const[i]
        assert cube_score(z, w) == query

print(f"PASS: {sheets} sheet/Jacobian identities, {orientations} path orientations, {vertices} cube vertices, and all grid identities.")
