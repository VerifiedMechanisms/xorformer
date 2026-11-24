#!/usr/bin/env python3
"""Exact checks over all Hamming-weight classes, not a proof of the general family."""
from fractions import Fraction as F
import json

records = []
for r in (1, 3, 5, 9, 21):
    M, R = r + 1, r * (r + 2)
    K = R + 1
    scores, first, second = [], [], []
    for u in range(r + 1):
        for v in range(r + 1):
            U, V = 2 * u - r, 2 * v - r
            L1, L2 = M * U + V, U + M * V
            assert (L1 > 0) == (U > 0)
            assert (L2 > 0) == (V > 0)
            B = K + L2
            assert 1 <= B <= 2 * R + 1
            a, b = F(L1), F(-K * L1, B)
            score = a + b
            assert score == F(L1 * L2, B)
            assert (score > 0) == ((U > 0) == (V > 0))
            scores.append(abs(score))
            first.append(abs(a))
            second.append(abs(b))
    margin = min(scores) / (max(first) + max(second))
    bound = F(1, R * (R + 2) * (2 * R + 1))
    assert margin >= bound
    records.append({"r": r, "weight_classes": (r + 1) ** 2,
                    "exact_margin": str(margin), "proved_lower_bound": str(bound)})
print(json.dumps(records, indent=2))
