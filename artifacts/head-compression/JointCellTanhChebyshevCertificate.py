#!/usr/bin/env python3
"""Exact interval audit of a narrow additive-residue Chebyshev claim.

Uses the rational interval arithmetic of the earlier coth certificate.
This disproves an all-orders Chebyshev assertion, not a polynomial root
bound and not any original-model upper-bound construction.
"""
from JointCellCothChebyshevCertificate import Interval, ONE, exp_positive, determinant


def kernel(x):
    e = exp_positive(Interval.rational(2) * x)
    return (e - ONE) / (e + ONE)


def main():
    for base, expected in [(1, -1), (2, 1)]:
        matrix = [[kernel(Interval.rational(base * (1000 + i) * (1000 + j), 1000000))
                   for j in range(10)] for i in range(10)]
        det = determinant(matrix)
        assert det.excludes_zero()
        actual = 1 if det.lo > 0 else -1
        assert actual == expected
        print(f"base={base}: exact rational interval determinant sign {actual:+d}")
    print("Tanh scaling family is not a Chebyshev system of every order.")
    print("No polynomial root bound is asserted or refuted.")


if __name__ == "__main__":
    main()
