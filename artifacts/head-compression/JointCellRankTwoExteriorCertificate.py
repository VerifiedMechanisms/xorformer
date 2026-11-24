#!/usr/bin/env python3
"""Exact finite certificate for a rank-two tensor Cauchy kernel.

This verifies rational endpoint signs used in a continuity proof.  It does
not compute the intervening algebraic parameter, prove a growing decoder,
or replace the original admissibility checks.  No optimizer or floating
point arithmetic is used.
"""

from fractions import Fraction as F
from itertools import permutations
import json
from math import prod
from pathlib import Path


def det3(matrix):
    return sum(
        (-1) ** sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))
        * prod(matrix[i][p[i]] for i in range(3))
        for p in permutations(range(3))
    )


def residues(left, right, center, spacing):
    poles = [a + b for a in left for b in right]
    assert len(set(poles)) == 9
    return [
        [
            prod(-a - b - center - i * spacing for i in range(8))
            / prod(a + b - other for other in poles if other != a + b)
            for b in right
        ]
        for a in left
    ]


def certificate():
    left = list(map(F, [0, 2947, 9807]))
    right = list(map(F, [0, 202, 1015]))
    budget = 3 * left[2] - 2 * left[1] + 3 * right[2] - 2 * right[1]
    assert budget == 26168
    centers = [F(1001, 1000) * budget, 2 * budget]
    assert centers[0] - budget == F(3271, 125)
    entries = []
    for spacing in [F(0), F(1, 10)]:
        determinants = []
        for center in centers:
            matrix = residues(left, right, center, spacing)
            determinant = det3(matrix)
            determinants.append(determinant)
            # Exact partial fraction identity at rational test values.  The
            # note proves it for every value and every center by residues.
            for z in map(F, [1, 10, 100, 1000, 10000]):
                score = sum(
                    matrix[a][b] / (z + left[a] + right[b])
                    for a in range(3)
                    for b in range(3)
                )
                target = prod(z - center - i * spacing for i in range(8)) / prod(
                    z + a + b for a in left for b in right
                )
                assert score == target
        assert determinants[0] < 0 < determinants[1]
        entries.append(
            dict(spacing=str(spacing), determinants=list(map(str, determinants)))
        )
    return dict(
        left_poles=list(map(str, left)),
        right_poles=list(map(str, right)),
        full_cube_gap_budget=str(budget),
        centers=list(map(str, centers)),
        endpoint_margin=str(centers[0] - budget),
        endpoint_checks=entries,
    )


if __name__ == "__main__":
    result = certificate()
    path = Path(__file__).with_name("joint-cell-rank-two-exterior-certificate.json")
    if path.exists():
        assert json.loads(path.read_text()) == result
    else:
        path.write_text(json.dumps(result, indent=2) + "\n")
    print("Exact endpoint signs, gap budget, and partial-fraction checks passed.")
