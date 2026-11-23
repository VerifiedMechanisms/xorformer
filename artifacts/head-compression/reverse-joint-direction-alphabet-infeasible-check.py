#!/usr/bin/env python3
"""Complete exact finite infeasibility test for one four-address pattern.

Run with heavy. This proves only the stated finite alphabet obstruction.
For each label assignment A has full column rank because its first four
rows form an invertible Cauchy-square matrix. Strict feasibility rescales
to sigma_i (A x)_i >= 1. A nonempty such pointed polyhedron has a vertex,
so some four independent active rows satisfy A_I x = sigma_I. Exhausting
all active sets is therefore complete, including degenerate arrangements.
"""
from fractions import Fraction as Q
from itertools import combinations, product
import importlib.util
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    'planes', Path(__file__).with_name('reverse-joint-affine-plane-search.py'))
planes = importlib.util.module_from_spec(spec)
spec.loader.exec_module(planes)


def feasible(matrix, signs):
    dimension = len(matrix[0])
    for active in combinations(range(len(matrix)), dimension):
        coefficients = planes.solve([matrix[i] for i in active],
                                    [Q(signs[i]) for i in active])
        if coefficients is not None and all(
                signs[i] * sum(a*b for a, b in zip(row, coefficients)) >= 1
                for i, row in enumerate(matrix)):
            return coefficients
    return None


def main():
    eps = Q(1, 10000)
    groups = 4
    kernel = [[1/(1-eps*(i+g+2))**2 for g in range(groups)]
              for i in range(groups)]
    assert len(planes.independent_columns(kernel)) == groups
    signs = [1, 1, -1, -1, 1, -1, 1, -1]
    # Sanity checks exercise both feasibility outcomes in exact arithmetic.
    assert feasible([[Q(1)], [Q(1)]], [1, 1]) is not None
    assert feasible([[Q(1)], [Q(1)]], [1, -1]) is None
    for power in (3, 5, 7, 9):
        delta = eps**power
        tried = 0
        for shifts in product((-1, 0, 1), repeat=groups):
            for orientations in product((-1, 1), repeat=groups):
                factors = [s*(1+delta*k) for s, k in zip(orientations, shifts)]
                matrix = kernel + [[kernel[i][g]*factors[g] for g in range(groups)]
                                   for i in range(groups)]
                assert feasible(matrix, signs) is None
                tried += 1
        assert tried == 6**groups
        print(f'epsilon=1/10000, delta=epsilon^{power}: '
              f'all {tried} assignments infeasible for (++--),(+-+-)', flush=True)


if __name__ == '__main__':
    main()
