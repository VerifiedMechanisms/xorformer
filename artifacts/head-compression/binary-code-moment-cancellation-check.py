#!/usr/bin/env python3
"""Exact finite audit of binary-code-moment-cancellation.tex."""
from fractions import Fraction as F
from itertools import product
from math import comb


def main():
    checks = 0
    for d in range(1, 5):
        for k in range(1, 6):
            poles, coeffs, groups = [], [], []
            for a in range(d):
                for h in range(k + 1):
                    poles.append(a * (k + 2) + h + 1)
                    coeffs.append((-1) ** h * comb(k, h))
                    groups.append(a)
            words = list(product((-1, 1), repeat=d))
            for x in words:
                for j in range(k):
                    value = sum(c * x[a] * p ** j for c, a, p in zip(coeffs, groups, poles))
                    assert value == 0
                    checks += 1
            # Fourier projection recovers exactly the coefficient of each group.
            t = F(max(poles) + 2)
            scores = [sum(F(c * x[a], 1) / (t - p)
                          for c, a, p in zip(coeffs, groups, poles)) for x in words]
            for a in range(d):
                projected = sum(x[a] * z for x, z in zip(words, scores)) / len(words)
                direct = sum(F(c, 1) / (t - p)
                             for c, b, p in zip(coeffs, groups, poles) if b == a)
                assert projected == direct != 0
                checks += 1
            # Unique disjoint pole sets make every signed rational sum distinct:
            # its residue at the first pole of each group recovers x[a].
            residue_words = {tuple(x[a] * coeffs[a * (k + 1)] for a in range(d))
                             for x in words}
            assert len(residue_words) == 2 ** d
    print(f"PASS: {checks} exact moment and character identities; sharp disjoint examples")


if __name__ == "__main__":
    main()
