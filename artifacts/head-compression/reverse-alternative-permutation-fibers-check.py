"""Exact tests of independent full-cube-admissible permutation fibers."""

from fractions import Fraction as Q
from itertools import permutations, product


def determinant(matrix):
    a = [[Q(t) for t in row] for row in matrix]
    value = Q(1)
    for k in range(len(a)):
        j = next((j for j in range(k, len(a)) if a[j][k]), None)
        if j is None:
            return Q(0)
        if j != k:
            a[k], a[j] = a[j], a[k]
            value = -value
        pivot = a[k][k]
        value *= pivot
        for j in range(k + 1, len(a)):
            ratio = a[j][k] / pivot
            for ell in range(k + 1, len(a)):
                a[j][ell] -= ratio * a[k][ell]
    return value


def check(d, r):
    h = 2 ** d
    intercept = (r + 3) * (h + 2)
    tokens = list(range(1, h + 1))
    addresses = [intercept - sum((2 ** k) * bit for k, bit in enumerate(y))
                 for y in product((0, 1), repeat=d)]
    perms = list(permutations(tokens))
    for perm in perms:
        c0 = [[Q(1, pole - token - 1) for token in perm] for pole in addresses]
        c1 = [[Q(1, pole - token - 2) for token in perm] for pole in addresses]
        block = [[Q(0)] * h + row for row in c0]
        block += [[v * v for v in row] + row for row in c1]
        assert determinant(block) == ((-1) ** h * determinant(c0) *
                                      determinant([[v * v for v in row] for row in c1]))
        assert determinant(block) != 0
    roots = 0
    for state in product(perms, repeat=r):
        roots += 1
        # Monotone affine denominators achieve their cube minima at all ones.
        assert all(min(addresses) - sum(state[i][j] + 1 for i in range(r)) - 1 > 0
                   for j in range(h))
        assert all(min(addresses) - token - r - 1 > 0 for token in tokens)
        for pole in addresses:
            for x in product((0, 1), repeat=r):
                size = sum(x)
                score = sum((Q(1, pole - sum((state[i][j] + 1) * x[i]
                                             for i in range(r)) - 1) for j in range(h)), Q(0))
                score -= sum((Q(1, pole - token - size - 1) for token in tokens), Q(0))
                if size == 0:
                    assert score < 0
                elif size == 1:
                    assert score == 0
                else:
                    assert score > 0
                # All z=0 numerators vanish at the specified roots.
    assert roots == len(perms) ** r
    return roots


count = sum(check(d, r) for d, r in [(1, 1), (1, 2), (1, 3), (2, 1), (2, 2)])
print(f"PASS: {count} exact roots; strict whole-cube denominator minima;")
print("      nonzero complete Jacobian blocks; all sample zeros and mixed-face signs")
