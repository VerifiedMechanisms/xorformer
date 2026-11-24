#!/usr/bin/env python3
"""Exact finite checks of the separated-majority product margin."""
from fractions import Fraction as F
from itertools import product
from math import prod

cases = 0
for length in range(1, 10):
    R = 8 * length
    for word in product((-1, 1), repeat=length):
        total = sum(word)
        if total == 0:
            continue
        u, v = [], []
        for h, sign in enumerate(word):
            scale = F(h + 2, h + 1)
            ratio = F(R**(1 + h % 3))
            if sign < 0:
                ratio = 1 / ratio
            u.append(scale * ratio)
            v.append(scale)
        p = [2*a + b for a, b in zip(u, v)]
        q = [a + 2*b for a, b in zip(u, v)]
        ratio = prod(p) / prod(q)
        assert ratio >= F(3, 2) if total > 0 else ratio <= F(2, 3)
        delta = min(p + q) / (8 * length)
        changed = prod(a + delta for a in p) / prod(b + delta for b in q)
        assert changed >= F(21, 16) if total > 0 else changed <= F(16, 21)
        cases += 1
print(f"PASS: {cases} exact separated-majority and positive-factor checks")
