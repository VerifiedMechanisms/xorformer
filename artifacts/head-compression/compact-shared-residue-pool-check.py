#!/usr/bin/env python3
"""Exact finite checks for compact-shared-residue-pool.tex.

These checks illustrate the theorem and check its divisibility identity;
the qualitative uniform compactness assertion is proved in the TeX file.
"""
from fractions import Fraction as Q
from itertools import product


def add(a, b):
    c = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return c


def mul(a, b):
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c


def evaluate(a, x):
    y = Q(0)
    for c in reversed(a):
        y = y * x + c
    return y


def linear_product(roots):
    a = [Q(1)]
    for r in roots:
        a = mul(a, [-r, Q(1)])
    return a


def monic_remainder(a, b):
    a = a[:]
    assert b[-1] == 1
    for i in range(len(a) - len(b), -1, -1):
        c = a[i + len(b) - 1]
        for j in range(len(b)):
            a[i + j] -= c * b[j]
    return a[:len(b) - 1]


checks = 0
for q in range(3, 10):
    poles = [Q(h, 1000000 * q) for h in range(1, q + 1)]
    times = list(map(Q, range(1, q + 1)))
    P = linear_product(poles)
    N = linear_product([Q(2 * h + 1, 2) for h in range(1, q)])
    basis = [linear_product(poles[:h] + poles[h + 1:]) for h in range(q)]
    residues = [evaluate(N, poles[h]) / evaluate(basis[h], poles[h])
                for h in range(q)]
    for signs in product((-1, 1), repeat=q):
        R = [Q(0)]
        for s, a, b in zip(signs, residues, basis):
            R = add(R, [s * a * x for x in b])
        difference = add(mul(R, R), [-x for x in mul(N, N)])
        assert not any(monic_remainder(difference, P))
        values = [evaluate(R, t) for t in times]
        assert all(values)
        changes = sum(x * y < 0 for x, y in zip(values, values[1:]))
        if len(set(signs)) == 1:
            assert changes == q - 1
        else:
            assert changes <= q // 2 - 1, (q, signs, changes)
        checks += 1
print(f"PASS: {checks} exact sign-flip numerators, divisibility and grid signs")
