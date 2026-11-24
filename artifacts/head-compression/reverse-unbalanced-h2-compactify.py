#!/usr/bin/env python3
"""Exact finite check: compactify a two-head five-row shattering certificate.

The input has two heads, five fixed (d_i,b_i) query pairs, and one
(p_j,a_j) witness for each of the 32 sign patterns. Its score is
sum_h (a_hj+b_hi)/(d_hi-p_hj). All arithmetic below uses Fraction.

For phi(t)=1/(q-t), the transformed ratio equals the old one plus
a/(p-q)-b/(d-q). Thus one affine row-plus-column correction restores
the entire table. This checker gives that correction a strictly
negative-slope denominator, with an exact error bound, so all three
heads satisfy the original strict whole-cube denominator conditions.
This is a finite 5-by-32 certificate, not an asymptotic construction.
"""

import itertools
import json
from fractions import Fraction as F
from pathlib import Path


def main():
    path = Path(__file__).with_name("reverse-unbalanced-h2-shattered.json")
    data = json.loads(path.read_text())
    d = [[F(*x) for x in row] for row in data["d"]]
    b = [[F(*x) for x in row] for row in data["b"]]
    witnesses = data["witnesses"]
    h_count, r, s = len(d), len(d[0]), len(witnesses)
    assert (h_count, r, s) == (2, 5, 32)
    assert {tuple(w["signs"]) for w in witnesses} == set(
        itertools.product((-1, 1), repeat=r)
    )
    p = [[F(*w["p"][h]) for w in witnesses] for h in range(h_count)]
    a = [[F(*w["a"][h]) for w in witnesses] for h in range(h_count)]
    signs = [[w["signs"][i] for w in witnesses] for i in range(r)]
    original = [[F(0) for _ in range(s)] for _ in range(r)]
    for h in range(h_count):
        assert max(p[h]) < min(d[h])
        for i in range(r):
            for j in range(s):
                original[i][j] += (a[h][j] + b[h][i]) / (d[h][i] - p[h][j])
    margin = min(signs[i][j] * original[i][j] for i in range(r) for j in range(s))
    assert margin > 0

    poles = (F(8535, 7549), F(11425, 9929))
    transformed = [[F(0) for _ in range(s)] for _ in range(r)]
    row_correction = [F(0) for _ in range(r)]
    col_correction = [F(0) for _ in range(s)]
    budgets = []
    minima = []
    m = r + s
    for h, pole in enumerate(poles):
        assert pole > max(d[h])
        dp = [1 / (pole - x) for x in d[h]]
        pp = [1 / (pole - x) for x in p[h]]
        bp = [b[h][i] / (d[h][i] - pole) ** 2 for i in range(r)]
        ap = [a[h][j] / (p[h][j] - pole) ** 2 for j in range(s)]
        beta = max(dp) - min(pp)
        row_slopes = [max(dp) - x for x in dp]
        col_slopes = [x - min(pp) for x in pp]
        slope_sum = sum(row_slopes) + sum(col_slopes)
        slack = beta - slope_sum
        assert slack > 0
        budgets.append(slope_sum / beta)

        # Add the same positive amount to every slope and twice that
        # amount to the constant. The two-one-hot grid is unchanged.
        pad = slack / (2 * m)
        row_slopes = [x + pad for x in row_slopes]
        col_slopes = [x + pad for x in col_slopes]
        beta += 2 * pad
        assert min(row_slopes + col_slopes) > 0
        cube_minimum = beta - sum(row_slopes) - sum(col_slopes)
        assert cube_minimum > 0
        minima.append(cube_minimum)
        for i in range(r):
            row_correction[i] += b[h][i] / (d[h][i] - pole)
            for j in range(s):
                denominator = beta - row_slopes[i] - col_slopes[j]
                assert denominator == dp[i] - pp[j] > 0
                value = (bp[i] + ap[j]) / denominator
                expected = (a[h][j] + b[h][i]) / (d[h][i] - p[h][j])
                expected += a[h][j] / (p[h][j] - pole)
                expected -= b[h][i] / (d[h][i] - pole)
                assert value == expected
                transformed[i][j] += value
        for j in range(s):
            col_correction[j] -= a[h][j] / (p[h][j] - pole)

    correction = [[row_correction[i] + col_correction[j] for j in range(s)] for i in range(r)]
    for i in range(r):
        for j in range(s):
            assert transformed[i][j] + correction[i][j] == original[i][j]
    maximum_correction = max(abs(x) for row in correction for x in row)
    eta = margin / (16 * (m + 1) * (margin + maximum_correction + 1))
    assert 0 < eta < F(1, 16 * (m + 1))
    assert 1 - m * eta > 0
    final_margin = min(
        signs[i][j] * (transformed[i][j] + correction[i][j] / (1 - 2 * eta))
        for i in range(r) for j in range(s)
    )
    assert final_margin > margin / 2 > 0
    print("Verified all 32 sign columns on five rows with three strict heads.")
    print("Normalized transformed slope budgets:", [float(x) for x in budgets])
    print("Positive full-cube denominator minima:", [float(x) for x in minima] + [float(1 - m * eta)])
    print("Original and final strict grid margins:", float(margin), float(final_margin))


if __name__ == "__main__":
    main()
