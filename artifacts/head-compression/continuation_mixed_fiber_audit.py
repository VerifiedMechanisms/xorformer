"""Exact rational audit of the mixed-column counterexample.

This script proves the finite sign claims by Fraction arithmetic. It does
not prove a worst-case head bound. See continuation-global.tex for the
symbolic sign proof and complete denominator-admissibility audit.
"""

from fractions import Fraction
from functools import reduce
from itertools import product
import json
from operator import mul


def prod(values):
    return reduce(mul, values, Fraction(1))


def main():
    f = Fraction
    eps = f(1, 1_000_000)
    nodes = [f(1) - f(i, 64) for i in range(4)]
    midpoint = f(125, 128)
    a, b, c = eps, 3 * eps, 4 * eps

    def row_poly(t):
        return prod(t - d for d in nodes)

    ratio = row_poly(a) / row_poly(b)
    target = (midpoint - 2 * a) / (midpoint - 2 * b)
    coefficient = ratio * (c - b) / (c - a)
    z = (coefficient * b + target * a) / (coefficient + target)
    poles = [a, z, b, c]
    assert a < z < b < c
    residues = [
        -row_poly(t) / prod(t - u for j, u in enumerate(poles) if j != i)
        for i, t in enumerate(poles)
    ]
    permutation = [2, 1, 0, 3]
    assert residues[0] / residues[2] == target

    min_denom = None
    all_scores = {}
    for u1, u2, v1, v2 in product((0, 1), repeat=4):
        d = 1 - f(u1, 64) - f(u2, 32)
        denoms = [
            d - poles[h] * v1 - poles[permutation[h]] * v2
            for h in range(4)
        ]
        assert all(denom > 0 for denom in denoms)
        min_denom = min(denoms) if min_denom is None else min(min_denom, *denoms)
        score = -1 + sum(
            (residues[h] * v1 + residues[permutation[h]] * v2) / denoms[h]
            for h in range(4)
        )
        all_scores[u1, u2, v1, v2] = score
        if v1 + v2 == 1:
            assert score == 0

    assert min_denom == f(61, 64) - 8 * eps
    mixed_scores = [all_scores[i % 2, i // 2, 1, 1] for i in range(4)]
    signs = [1 if value > 0 else -1 if value < 0 else 0 for value in mixed_scores]
    assert signs == [1, 1, -1, -1]
    print(json.dumps({
        "status": "exact rational counterexample; no asymptotic theorem",
        "lambda_2": str(z),
        "minimum_cube_denominator": str(min_denom),
        "single_memory_scores_exactly_zero": True,
        "mixed_fiber_signs": signs,
        "mixed_fiber_exact_scores": [str(value) for value in mixed_scores],
        "mixed_fiber_float_scores_for_orientation_only": [float(value) for value in mixed_scores],
    }, indent=2))


if __name__ == "__main__":
    main()
