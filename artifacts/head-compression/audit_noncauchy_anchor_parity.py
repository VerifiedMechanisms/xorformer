#!/usr/bin/env python3
"""Exact finite obstruction for one non-Cauchy four-head anchor reader.

This is not a general lower bound and is not a numerical LP certificate.
Every matrix operation and every sign check below uses rational arithmetic.
"""

import itertools
import json

import sympy as sp


def main():
    h_count = 4
    epsilon = sp.Rational(1, 1000)
    anchor_slopes = [
        [8, 1, 9, 4],
        [8, 1, 1, 1],
        [2, 5, 9, 5],
        [7, 3, 7, 3],
    ]
    query_slopes = [6, 1, 8, 5]
    permutations = list(itertools.permutations(range(1, h_count + 1)))
    signs = sp.Matrix([
        (-1) ** sum(p[i] > p[j] for i in range(h_count)
                    for j in range(i + 1, h_count))
        for p in permutations
    ])

    feature_rows = []
    for p in permutations:
        matrix = sp.Matrix(h_count, h_count, lambda i, h:
                           1 / (1 - epsilon * (anchor_slopes[i][h] + p[h])))
        assert matrix.det() != 0
        query = sp.Matrix([[1 / (1 - epsilon * (query_slopes[h] + p[h]))
                            for h in range(h_count)]])
        weights = query * matrix.inv()
        # Coefficients of all 16 anchor numerators, four query numerators,
        # and the final scalar bias, after solving all anchor equations.
        feature_rows.append([
            -weights[i] * matrix[i, h]
            for i in range(h_count) for h in range(h_count)
        ] + list(query) + [sp.Integer(1)])
    features = sp.Matrix(feature_rows)
    _, columns = features.rref()
    assert len(columns) == 14
    basis = features[:, list(columns)]
    dual_equations = basis.T * sp.diag(*list(signs))
    reduced, pivots = dual_equations.rref()
    free = [j for j in range(len(permutations)) if j not in pivots]
    dual = sp.ones(len(permutations), 1)
    for i, j in enumerate(pivots):
        dual[j] = -sum(reduced[i, k] for k in free)

    assert all(sp.Rational(99, 100) < value < sp.Rational(101, 100)
               for value in dual)
    assert features.T * sp.diag(*list(signs)) * dual == sp.zeros(21, 1)

    # Five row bits and one memory bit for each of the 24 permutations.
    # Every slope is positive; the minimum occurs at the all-one vertex.
    minima = [1 - epsilon * (
        sum(row[h] for row in anchor_slopes) + query_slopes[h]
        + sum(p[h] for p in permutations)) for h in range(h_count)]
    assert min(minima) > sp.Rational(9, 10)
    print(json.dumps({
        "states": len(permutations),
        "exact_feature_rank": len(columns),
        "positive_dual_bounds": ["99/100", "101/100"],
        "all_cube_denominator_minimum": str(min(minima)),
        "parity_strictly_unreadable": True,
    }))


if __name__ == "__main__":
    main()
