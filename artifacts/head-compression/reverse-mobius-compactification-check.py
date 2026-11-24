#!/usr/bin/env python3
"""Exact checks for the written Mobius identity and normalized box construction.

This verifies finite rational instances, not an asymptotic compiler.
"""
from fractions import Fraction as F
from itertools import product


def phi(t, alpha, beta, gamma, delta):
    return (alpha * t + beta) / (gamma * t + delta)


def cross_ratio(lo, hi, lower_query, upper_query):
    return ((hi - lo) * (upper_query - lower_query)
            / ((lower_query - hi) * (upper_query - lo)))


checks = 0
for p, d, a, b, gamma in product(
        (F(1, 7), F(2, 7)), (F(5, 7), F(6, 7)),
        (F(-3), F(2)), (F(-1), F(4)), (F(-1), F(1))):
    alpha, beta, delta = F(1), F(0), F(2)
    determinant = alpha * delta - beta * gamma
    gp, gd = gamma * p + delta, gamma * d + delta
    transformed = ((determinant * a / gp**2 + determinant * b / gd**2)
                   / (phi(d, alpha, beta, gamma, delta)
                      - phi(p, alpha, beta, gamma, delta)))
    assert transformed == (a + b) / (d - p) + gamma * a / gp - gamma * b / gd
    checks += 1

lo, hi, lower_query, upper_query = F(1, 8), F(3, 8), F(6, 8), F(7, 8)
chi = cross_ratio(lo, hi, lower_query, upper_query)
for numerator in range(1, 12):
    P = F(numerator, 13)
    u, span = hi - lo, upper_query - lo
    C = (P * span - u) / (span * u * (1 - P))
    transform = lambda t: (C * span + 1) * (t - lo) / (span * (C * (t - lo) + 1))
    Q = chi * (1 - P) / (P + chi)
    assert transform(lo) == 0 and transform(upper_query) == 1
    assert transform(hi) == P and transform(lower_query) == 1 - Q
    assert cross_ratio(*(transform(t) for t in (lo, hi, lower_query, upper_query))) == chi
    assert 0 < P and 0 < Q and P + Q < 1
    checks += 1

for r, s in product(range(2, 10), repeat=2):
    chi = F(1, 16 * r * s)
    P = F(1, 2 * r)
    Q = chi * (1 - P) / (P + chi)
    assert P * Q == chi * (1 - P - Q)
    assert r * P + s * Q < F(3, 4)
    checks += 1

print(f"{checks} exact rational identity, cross-ratio, and box-budget checks passed")
