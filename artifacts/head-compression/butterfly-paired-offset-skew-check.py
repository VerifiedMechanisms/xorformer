#!/usr/bin/env python3
"""Exact finite checks of the one-level matched-center identity."""
from fractions import Fraction as F
from itertools import product


def paired(d, gap, kappa, pole, numerator):
    return ((numerator + kappa) / (d - pole)
            - (numerator - kappa) / (d + gap - pole))


checks = words = 0
for q in range(2, 9):
    poles = [F(i, 100) for i in range(q)]
    centers = [F(i*i - 2*i, 7) for i in range(q)]
    kappas = [F(2*i + 1, 11) for i in range(q)]
    gap, total = F(1, 10), F(3)
    delta = []
    for s in range(q):
        row = []
        for r in range(q):
            d = total - poles[s]
            offset = centers[r] - centers[s]
            value = (
                paired(d, gap, kappas[s], poles[r], offset + kappas[r])
                - paired(d, gap, kappas[s], poles[r] + gap,
                         offset - kappas[r])
            )
            x = total - poles[s] - poles[r]
            kernel_k = 2*gap**2 / (x * (x**2 - gap**2))
            kernel_l = 2*gap / (x**2 - gap**2)
            claimed = ((centers[s] - centers[r]) * kernel_k
                       + (kappas[r] - kappas[s]) * kernel_l)
            assert value == claimed
            row.append(value)
            checks += 1
        delta.append(row)
    assert all(delta[s][r] == -delta[r][s]
               for s in range(q) for r in range(q))
    for sigma in product((-1, 1), repeat=q):
        if sum(sigma):
            continue
        score = [sum(delta[s][r] * sigma[r] for r in range(q)) + F(5, 7)
                 for s in range(q)]
        assert sum(sigma[s] * score[s] for s in range(q)) == 0
        words += 1
print(f"PASS: {checks} exact pair identities and {words} balanced words")
