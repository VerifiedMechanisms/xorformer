#!/usr/bin/env python3
"""Rational interval counterexample to a coth scaling Chebyshev lemma.

No floating point arithmetic is used in the assertions.  The two ten by
 ten determinants have the same increasing scale parameters and opposite
 signs at increasing sample sets.  This does not prove a superlinear zero
 lower bound for ratios of hyperbolic-sine products.
"""
from dataclasses import dataclass

DIGITS = 700
SCALE = 10 ** DIGITS

def ceiling(a, b):
    return -((-a) // b)

@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    @staticmethod
    def rational(n, d=1):
        assert d > 0
        return Interval(n * SCALE // d, ceiling(n * SCALE, d))

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        products = [a * b for a in [self.lo, self.hi] for b in [other.lo, other.hi]]
        return Interval(min(products) // SCALE, ceiling(max(products), SCALE))

    def reciprocal(self):
        assert self.lo > 0 or self.hi < 0
        return Interval(SCALE * SCALE // self.hi,
                        ceiling(SCALE * SCALE, self.lo))

    def __truediv__(self, other):
        return self * other.reciprocal()

    def excludes_zero(self):
        return self.lo > 0 or self.hi < 0

ONE = Interval.rational(1)
ZERO = Interval.rational(0)

def exp_positive(x):
    assert 0 <= x.lo <= x.hi <= 9 * SCALE
    term = ONE
    total = ONE
    for k in range(1, 601):
        term = term * x / Interval.rational(k)
        total = total + term
    next_term = term * x / Interval.rational(601)
    tail = next_term / (ONE - x / Interval.rational(602))
    return Interval(total.lo, total.hi + tail.hi)

def kernel(x):
    e = exp_positive(Interval.rational(2) * x)
    return x * (e + ONE) / (e - ONE) - ONE

def determinant(matrix):
    a = [row[:] for row in matrix]
    answer = ONE
    for i in range(len(a)):
        candidates = [j for j in range(i, len(a)) if a[j][i].excludes_zero()]
        assert candidates
        pivot = max(candidates, key=lambda j: min(abs(a[j][i].lo), abs(a[j][i].hi)))
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            answer = -answer
        diagonal = a[i][i]
        answer = answer * diagonal
        for j in range(i + 1, len(a)):
            scale = a[j][i] / diagonal
            for k in range(i + 1, len(a)):
                a[j][k] = a[j][k] - scale * a[i][k]
    return answer

def main():
    for base, expected in [(1, -1), (4, 1)]:
        matrix = [[kernel(Interval.rational(base * (1000 + i) * (1000 + j), 1000000))
                   for j in range(10)] for i in range(10)]
        det = determinant(matrix)
        assert det.excludes_zero()
        actual = 1 if det.lo > 0 else -1
        assert actual == expected
        print(f"base={base}: exact rational interval determinant sign {actual:+d}")
    print("Coth scaling family is not a Chebyshev system of every order.")
    print("No general product-ratio root bound is asserted or refuted.")

if __name__ == '__main__':
    main()
