#!/usr/bin/env python3
"""Exact rational constants in the uniform vanilla-three tensor exclusion."""
from fractions import Fraction as F


def constants():
    b = [[(F(i) ** (h + 3) - F(15, 2) ** (h + 3)) / 10**9
          for i in range(1, 15)] for h in range(3)]
    vandermonde = F(34560, 10**39)
    mixed = min(min(max(row), -min(row)) for row in b)
    nonzero = [min(abs(x) for x in row) for row in b]
    cross_minor = 4 * vandermonde**2 * (nonzero[0] * nonzero[1] * nonzero[2])**2
    hessian = 4 * mixed**6 * vandermonde**2 / (12**11 * 10**10)
    inverse = 1 + 240 * 19**5 / cross_minor
    radius = min(F(1), cross_minor / (10000 * 19**5),
                 1 / (10**6 * inverse**2), hessian / (10**14 * inverse**3))
    return vandermonde, mixed, cross_minor, hessian, inverse, radius


def main():
    v, delta, d, lam, k, radius = constants()
    assert min(v, delta, d, lam, k, radius) > 0
    assert k >= 1
    # Determinant perturbation leaves every selected cross block invertible.
    assert 4320 * 19**5 * radius < d / 2
    # First Schur recovery bounds mixed repeated-index coefficients.
    first = 2000 * k + 500000 * k**2
    assert first <= 502000 * k**2
    assert first * radius < 1
    # Second recovery bounds the pure cubes; this common bound also covers
    # first-recovery errors and the original squarefree errors.
    second = 6000 * first * k + 2000000 * k**2
    assert second < 10**10 * k**3
    assert max(F(1), first, second) * radius < lam / 2352
    assert radius > F(1, 2**2000)
    print('exact quantitative checks passed: tensor exclusion radius > 2^-2000')
    print('scope: every oriented three-head cubic tensor, with arbitrary untied coefficients')


if __name__ == '__main__':
    main()
