#!/usr/bin/env python3
"""Exact finite checks for local-histogram-zero-branches.tex.

This verifies identities, derivative ranks, and two finite orthant claims.
It does not prove asymptotic sign coverage or a small-epsilon germ.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import permutations
from math import factorial

from flint import fmpq, fmpq_mat


def qmat(rows):
    return fmpq_mat([[fmpq(x.numerator, x.denominator) for x in row]
                     for row in rows])


def signature(pi, rhos, signs=None):
    return tuple(tuple(sorted((pi[h] + rho[h],
                               signs[l][h] if signs else 1)
                              for h in range(len(pi))))
                 for l, rho in enumerate(rhos))


def fiber_partition(H, rhos, signs=None):
    out = defaultdict(list)
    for pi in permutations(range(1, H + 1)):
        out[signature(pi, rhos, signs)].append(pi)
    return out


def derivative(pi, rhos, queries, eps):
    rows = []
    for group, t in queries:
        gaps = [t - eps * (pi[h] + rhos[group][h])
                for h in range(len(pi))]
        assert all(x > 0 for x in gaps)
        rows.append([1 / x for x in gaps] + [1 / x**2 for x in gaps])
    return rows


def normal_signs(matrix):
    n = len(matrix[0])
    assert len(matrix) == n + 1
    cofactors = [(-1)**i * qmat(matrix[:i] + matrix[i + 1:]).det()
                for i in range(n + 1)]
    assert all(cofactors)
    assert all(sum(cofactors[i] * fmpq(matrix[i][j].numerator,
                                     matrix[i][j].denominator)
                   for i in range(n + 1)) == 0 for j in range(n))
    word = tuple((x > 0) - (x < 0) for x in cofactors)
    return tuple(x * word[0] for x in word)


def main():
    identity_checks = 0
    for H in range(2, 8):
        rho = tuple(range(1, H + 1))
        partition = fiber_partition(H, [rho])
        largest = max(partition.values(), key=len)
        assert len(partition) <= 2**(3 * H)
        assert len(largest) * len(partition) >= factorial(H)
        for pi in largest:
            for t in (F(1), F(7, 6), F(9, 8)):
                score = sum(1 / (t - F(1, 1000) * (pi[h] + rho[h]))
                            for h in range(H))
                baseline = sum(1 / (t - F(1, 1000) * (largest[0][h] + rho[h]))
                               for h in range(H))
                assert score == baseline
                identity_checks += 1
        pi = largest[0]
        pure_queries = [(0, 1 - F(j + 1, 10000)) for j in range(2 * H)]
        assert qmat(derivative(pi, [(0,) * H], pure_queries, F(1, 1000))).det()
        print(f'H={H}: {len(partition)} signatures; largest fiber {len(largest)}')

    H = 6
    rhos = [tuple(range(1, H + 1)), (3, 1, 6, 2, 5, 4)]
    signs = [(1,) * H, (1, -1, 1, -1, -1, 1)]
    partition = fiber_partition(H, rhos, signs)
    for family in partition.values():
        for pi in family[1:]:
            for l in range(2):
                score = lambda p: sum(F(signs[l][h]) /
                                     (1 - F(1, 1000) * (p[h] + rhos[l][h]))
                                     for h in range(H))
                assert score(pi) == score(family[0])
                identity_checks += 1

    H = 3
    family = [(2, 3, 1), (3, 1, 2)]
    rhos = [(0,) * H, tuple(range(1, H + 1))]
    queries = [(0, 1 - F(j + 1, 1000)) for j in range(4)]
    queries += [(1, 1 - F(j + 1, 1000)) for j in range(3)]
    normals = [normal_signs(derivative(pi, rhos, queries, F(1, 100)))
               for pi in family]
    assert normals[0] == normals[1]
    print('H=3: both tangent spaces meet precisely the same 126/128 orthants')

    H = 4
    family = [(3, 4, 2, 1), (4, 2, 3, 1), (4, 3, 1, 2)]
    rhos = [(0,) * H, tuple(range(1, H + 1))]
    queries = [(0, F(2461, 2500)), (0, F(1977, 2000)),
               (1, F(9989, 10000)), (1, F(9869, 10000)),
               (0, F(991, 1000)), (1, F(4939, 5000)),
               (1, F(9901, 10000)), (1, F(491, 500)),
               (0, F(4949, 5000))]
    for denominator in (100, 10000, 10**8):
        normals = [normal_signs(derivative(pi, rhos, queries,
                                          F(1, denominator))) for pi in family]
        assert normals[0] != normals[1]
        print(f'H=4 epsilon=1/{denominator}: union meets all 512/512 orthants')
    print(f'Passed {identity_checks} exact score identities and all rank/normal checks.')


if __name__ == '__main__':
    main()
