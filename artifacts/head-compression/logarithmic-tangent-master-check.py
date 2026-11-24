#!/usr/bin/env python3
"""Exact finite checks for logarithmic-tangent-master.tex.

The all-dimension induction is a written proof, not inferred from these tests.
No floating-point arithmetic or nonlinear feasibility solver is used.
"""

from itertools import combinations
from math import comb, factorial
import json
from pathlib import Path

import sympy as sp


def data(b):
    n = len(b)
    b = tuple(map(sp.Rational, b))
    subsets = [S for k in range(1, n + 1)
               for S in combinations(range(n), k)]
    den = {S: 1 + sum(b[j] for j in S) for S in subsets}
    matrix = sp.Matrix([
        [sum(1 / den[S] for S in subsets if len(S) == k and i in S)
         for k in range(1, n + 1)] for i in range(n)
    ])
    kernel = matrix.nullspace()
    assert len(kernel) == 1
    lam = kernel[0] * (2 / kernel[0][0])
    assert matrix * lam == sp.zeros(n, 1)
    hessian = sp.Matrix([
        [-sum(lam[len(S) - 1] / den[S] ** 2
              for S in subsets if i in S and j in S)
         for j in range(n)] for i in range(n)
    ])
    determinant = hessian.det()
    beta = sum(comb(n - 1, k - 1) * lam[k - 1]
               for k in range(1, n + 1))
    assert determinant != 0 and beta != 0
    empty_weight = -sum(comb(n, k) * lam[k - 1]
                        for k in range(1, n + 1))
    assert empty_weight + sum(lam[len(S) - 1] / den[S]
                              for S in subsets) == 0
    return {
        "dimension": n,
        "point": list(map(str, b)),
        "weights": list(map(str, lam)),
        "gradient_matrix_rank": matrix.rank(),
        "hessian_determinant": str(determinant),
        "binomial_moment": str(beta),
        "empty_vertex_weight": str(empty_weight),
        "distinct_regular_permutations": factorial(n) // 2,
    }


def symbolic_first_step():
    t = sp.symbols("T", positive=True)
    b = (sp.Integer(1), sp.Integer(1), t)
    lam = (sp.Integer(2), -3 * (t + 2) / (t + 1),
           4 * (t + 3) / (t + 1))
    subsets = [S for k in range(1, 4)
               for S in combinations(range(3), k)]
    den = {S: 1 + sum(b[j] for j in S) for S in subsets}
    for i in range(3):
        assert sp.factor(sum(lam[len(S) - 1] / den[S]
                             for S in subsets if i in S)) == 0
    hessian = sp.Matrix([
        [-sum(lam[len(S) - 1] / den[S] ** 2
              for S in subsets if i in S and j in S)
         for j in range(3)] for i in range(3)
    ])
    expected = -(t - 1) ** 3 * (t + 4) / (
        6 * (t + 1) ** 4 * (t + 2) ** 2 * (t + 3))
    assert sp.factor(hessian.det() - expected) == 0
    assert sp.factor(sum(comb(2, k) * lam[k] for k in range(3))
                     - 2 / (t + 1)) == 0


def main():
    symbolic_first_step()
    examples = [data([1, 1] + list(range(2, n))) for n in range(2, 11)]
    report = {
        "status": "exact rational and symbolic finite verification",
        "scope": "written all-dimension induction is not a computational inference",
        "symbolic_first_induction_step_checked": True,
        "examples": examples,
    }
    path = Path(__file__).with_suffix(".json")
    path.write_text(json.dumps(report, indent=2) + "\n")
    for item in examples:
        print("n={dimension}: rank={gradient_matrix_rank}, "
              "regular orbit size={distinct_regular_permutations}".format(**item))
    print("All exact checks passed.")


if __name__ == "__main__":
    main()
