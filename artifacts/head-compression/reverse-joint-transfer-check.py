#!/usr/bin/env python3
"""Small exact checks for reverse-joint-transfer-audit.tex.

This is identity verification, not evidence of universal compression.
Only Python's standard-library exact rational arithmetic is used.
"""

from fractions import Fraction as Q
from itertools import product


def additive(a):
    return all(
        a[i][j] + a[0][0] == a[i][0] + a[0][j]
        for i in range(len(a))
        for j in range(len(a[0]))
    )


def mobius(x, a, b, c, d):
    return (a * x + b) / (c * x + d)


def check_cauchy_covariance():
    a, b, c, d = map(Q, (2, 3, 1, 11))
    for u, v in product(map(Q, (1, 2, 4)), repeat=2):
        lhs = mobius(u, a, b, c, d) - mobius(-v, a, b, c, d)
        rhs = (a * d - b * c) * (u + v) / ((c * u + d) * (d - c * v))
        assert lhs == rhs


def check_independent_orders():
    # The theorem is general; this finite check catches arithmetic and
    # direction errors in the concrete example, without proving it.
    row_orders = ((1, 2, 4), (1, 4, 2))
    columns = (1, 3, 5)
    choices = tuple(map(Q, (1, 2, 3)))
    for alpha in product(choices, repeat=3):
        for beta in product(choices, repeat=3):
            matrices = [
                [[alpha[i] * beta[j] * (rows[i] + columns[j])
                  for j in range(3)] for i in range(3)]
                for rows in row_orders
            ]
            if all(map(additive, matrices)):
                assert len(set(alpha)) == len(set(beta)) == 1


def check_arbitrary_numerator_one_slot():
    # A high-degree numerator still clears into the four claimed features.
    def psi(t):
        return t ** 17 - 3 * t ** 9 + 7 * t ** 2 - 2

    for t in map(Q, (-2, -1, 0, 1, 2)):
        for a, b, c in product(map(Q, (-3, 0, 2)), repeat=3):
            d, e = Q(5), Q(7)
            score = c + (a - psi(t)) / (d - t) - (b - psi(t)) / (e - t)
            cleared = ((d - e) * psi(t) + c * t ** 2
                       + (-a + b - c * (d + e)) * t
                       + a * e - b * d + c * d * e)
            assert score * (d - t) * (e - t) == cleared
    # Check the actual divided-difference specialization, not merely
    # arbitrary affine numerators.
    for d, e, t in product(map(Q, (5, 6, 7)),
                           map(Q, (8, 9)), map(Q, (-1, 0, 1, 2))):
        difference = (psi(d) - psi(t)) / (d - t) - (psi(e) - psi(t)) / (e - t)
        cleared = ((d - e) * psi(t) + (-psi(d) + psi(e)) * t
                   + psi(d) * e - psi(e) * d)
        assert difference * (d - t) * (e - t) == cleared


def check_shared_baseline():
    # All 16 two-by-two tables. The common baseline has strictly negative
    # slopes, as does each row-specific denominator. Its cube minimum is 1.
    r = s = 2
    p, epsilon, delta = Q(6), Q(1), Q(1)
    for labels in product((-1, 1), repeat=r * s):
        table = [labels[i * s:(i + 1) * s] for i in range(r)]

        def score(z, w):
            denominator = p - epsilon * (sum(z) + sum(w))
            linear = [sum(Q(table[i][j]) * w[j] for j in range(s))
                      for i in range(r)]
            assert denominator > 0
            assert all(denominator - delta * z[i] > 0 for i in range(r))
            return (sum(linear[i] / (denominator - delta * z[i])
                        for i in range(r)) - sum(linear) / denominator)

        for z, w in product(product((0, 1), repeat=r),
                            product((0, 1), repeat=s)):
            value = score(z, w)
            if not any(z) or not any(w):
                assert value == 0
            if sum(z) == sum(w) == 1:
                i, j = z.index(1), w.index(1)
                d_grid = p - 2 * epsilon
                assert value == delta * table[i][j] / (d_grid * (d_grid - delta))
                assert table[i][j] * value > 0


if __name__ == "__main__":
    check_cauchy_covariance()
    check_independent_orders()
    check_arbitrary_numerator_one_slot()
    check_shared_baseline()
    print("Exact checks passed: Cauchy covariance, independent row orders, "
          "arbitrary-numerator one-slot clearing, all 2x2 baseline tables.")
