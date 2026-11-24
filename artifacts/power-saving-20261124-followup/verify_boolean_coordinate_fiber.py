#!/usr/bin/env python3
"""Exact two-head Boolean coordinate-fiber certificate, with no numerical roots.

All score computations use fractions.Fraction. Jacobian nonsingularity is
checked by integer fraction-free elimination after positive row scaling.
This is a finite computation, not a Lean theorem.
"""

from fractions import Fraction as Q
import json


N_BITS = 6
SAMPLE_CODES = [*range(7), *range(8, 20), *range(32, 36), 56, 57]
BIAS = -Q(31, 60)


def bits(code):
    return tuple((code >> (N_BITS - 1 - i)) & 1 for i in range(N_BITS))


def weights(swapped):
    return [
        [2 if swapped else 1, 2, 1, 3, 4, 5],
        [1 if swapped else 2, 1, 2, 3, 4, 5],
    ]


def denominators(swapped, x):
    return [1 + sum(a * b for a, b in zip(w, x)) for w in weights(swapped)]


def score(swapped, x):
    return BIAS + sum((Q(1, b) for b in denominators(swapped, x)), Q(0))


def scaled_jacobian(swapped):
    """Rows of diag(B1^2 B2^2) times the normalized evaluation Jacobian.

    Parameter order: b, u1[0:6], w1[0:6], u2[0:6], w2[0:6].
    The normalized score is b + sum_h (u_h dot x)/(1+w_h dot x).
    At the displayed representation b=BIAS+2 and u_h=-w_h.
    """
    rows = []
    for code in SAMPLE_CODES:
        x = bits(code)
        b1, b2 = denominators(swapped, x)
        rows.append(
            [b1 * b1 * b2 * b2]
            + [xi * b1 * b2 * b2 for xi in x]
            + [(b1 - 1) * xi * b2 * b2 for xi in x]
            + [xi * b2 * b1 * b1 for xi in x]
            + [(b2 - 1) * xi * b1 * b1 for xi in x]
        )
    return rows


def bareiss_det(matrix):
    """Exact determinant and pivot record using fraction-free elimination."""
    a = [row[:] for row in matrix]
    n = len(a)
    assert all(len(row) == n for row in a)
    previous, sign, pivots, swaps = 1, 1, [], []
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0, pivots, swaps
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
            swaps.append([k, pivot_row])
        pivot = a[k][k]
        pivots.append(pivot)
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
        for i in range(k + 1, n):
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1], pivots, swaps


def main():
    cube = [bits(code) for code in range(1 << N_BITS)]
    scores = [[score(swapped, x) for x in cube] for swapped in (False, True)]
    agreement_codes = [code for code, x in enumerate(cube) if x[0] == 0 or x[1] == x[2]]
    assert len(agreement_codes) == 48
    assert all(scores[0][code] == scores[1][code] for code in agreement_codes)
    assert all(code in agreement_codes for code in SAMPLE_CODES)
    assert len(set(SAMPLE_CODES)) == 25
    difference_codes = [code for code in range(64) if (scores[0][code] > 0) != (scores[1][code] > 0)]
    assert difference_codes == [40, 48]
    assert scores[0][48] == -Q(1, 60) and scores[1][48] == Q(1, 60)
    amplitude = abs(BIAS) + 2
    branches = []
    for swapped in (False, True):
        det, pivots, swaps = bareiss_det(scaled_jacobian(swapped))
        assert det == 21707597330497142784000000000000
        min_score = min(abs(v) for v in scores[swapped])
        assert min_score == Q(1, 60)
        assert min_score / amplitude == Q(1, 151)
        assert all(b > 0 for x in cube for b in denominators(swapped, x))
        assert all(max(Q(1, denominators(swapped, x)[h]) for x in cube) == 1 for h in range(2))
        branches.append({
            "swapped": swapped,
            "weights": weights(swapped),
            "minimum_absolute_score": str(min_score),
            "full_cube_amplitude": str(amplitude),
            "relative_margin": str(min_score / amplitude),
            "integer_scaled_jacobian_determinant": str(det),
            "bareiss_pivots": [str(p) for p in pivots],
            "bareiss_row_swaps": swaps,
            "truth_table_in_code_order": "".join("1" if v > 0 else "0" for v in scores[swapped]),
        })
    print(json.dumps({
        "arithmetic": "exact integers and fractions.Fraction",
        "scope": "finite certificate, not kernel checked",
        "sample_codes_most_significant_bit_first": SAMPLE_CODES,
        "agreement_codes": agreement_codes,
        "different_label_codes": difference_codes,
        "bias": str(BIAS),
        "normalized_chart_bias": str(BIAS + 2),
        "branches": branches,
    }, indent=2))


if __name__ == "__main__":
    main()
