#!/usr/bin/env python3
"""Exact finite checks of the real triangular expansion, not a head bound."""

from fractions import Fraction
from itertools import product


def add_term(poly, exponent, value):
    value = poly.get(exponent, Fraction(0)) + value
    if value:
        poly[exponent] = value
    else:
        poly.pop(exponent, None)


def multiply(left, right):
    result = {}
    for (a, b), x in left.items():
        for (c, d), y in right.items():
            add_term(result, (a | c, b | d), x * y)
    return result


def quadrant(a, b, r, s):
    return {(a ^ (1 << i), b | (1 << j))
            for i in range(r) if a & (1 << i)
            for j in range(s) if not b & (1 << j)}


def audit(r, s):
    centers = sorted(product(range(1 << r), range(1 << s)),
                     key=lambda ab: (-sum(z.bit_count() for z in ab),
                                     -ab[0].bit_count(), ab))
    interior = {(a, b) for a, b in centers if a != (1 << r) - 1 and b}
    remainder = {ab: Fraction((19 * ab[0] + 13 * ab[1]) % 23 - 11, 7)
                 for ab in interior}
    remainder = {ab: x for ab, x in remainder.items() if x}
    initial = remainder.copy()
    assembled = {}
    removed = set()
    for a, b in centers:
        expansion = {(0, b): Fraction(1)}
        for i in range(r):
            if not a & (1 << i):
                continue
            factor = {(1 << i, 0): Fraction(1)}
            for j in range(s):
                if not b & (1 << j):
                    add_term(factor, (0, 1 << j),
                             remainder.get((a ^ (1 << i), b | (1 << j)), 0))
            expansion = multiply(expansion, factor)
        add_term(expansion, (a, b), -1)
        current = quadrant(a, b, r, s)
        for exponent in current:
            assert expansion.get(exponent, 0) == remainder.get(exponent, 0)
        for exponent, value in expansion.items():
            assert exponent not in removed
            assert exponent in interior
            if exponent not in current:
                assert exponent[0].bit_count() <= a.bit_count() - 2
                assert sum(z.bit_count() for z in exponent) <= a.bit_count() + b.bit_count()
            add_term(remainder, exponent, -value)
            add_term(assembled, exponent, value)
        removed |= current
        assert not set(remainder) & removed
    assert not remainder
    assert assembled == initial
    print(f"r={r}, s={s}: exact expansion and triangular invariants passed")


if __name__ == "__main__":
    for block_sizes in [(1, 1), (2, 2), (2, 3), (3, 3), (4, 3)]:
        audit(*block_sizes)
