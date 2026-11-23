#!/usr/bin/env python3
"""Exact small checks of the cleared numerator rank expansion."""
from fractions import Fraction as Q
from itertools import product

checked = 0
for H in range(1, 4):
    k = 5
    al = [[Q(1 + h + i, 100 * (H + k)) for i in range(k)] for h in range(H)]
    be = [[Q(1 + 2 * h + j, 100 * (H + k)) for j in range(k)] for h in range(H)]
    ar = [[Q((h + 1) * (i + 1) - 4) for i in range(k)] for h in range(H)]
    ac = [[Q(h - 2 * j + 1) for j in range(k)] for h in range(H)]
    for h in range(H):
        assert sum(al[h]) + sum(be[h]) < 1
    for i in range(k):
        for j in range(k):
            direct = Q(0)
            expanded = Q(0)
            for h in range(H):
                factors = [(ar[h][i], ac[h][j])]
                factors += [(1 - al[g][i], -be[g][j]) for g in range(H) if g != h]
                value = Q(1)
                for pair in factors:
                    value *= sum(pair)
                direct += value
                for choices in product((0, 1), repeat=H):
                    value = Q(1)
                    for pair, choice in zip(factors, choices):
                        value *= pair[choice]
                    expanded += value
            assert direct == expanded
            checked += 1

# Exact Bernoulli and diagonal-dominance margins, including H=1.
for H in range(1, 31):
    assert (1 - Q(1, 2 * H)) ** H >= Q(1, 2)
for k in range(1, 101):
    epsilon = Q(1, 2 * k + 1)
    assert (k - 1) * epsilon < (1 - epsilon) / 2

print(f"PASS: {checked} exact rank-expansion checks and 130 margin checks.")
