#!/usr/bin/env python3
"""Exact formal-series verification of a compact shared-pool obstruction.

Requires python-flint.  No optimization solver is used.  Gaussian elimination
specifies a vector of rational functions, while exact truncated arithmetic
certifies its positive leading coefficients and nonzero pivots.  This is a
written-proof certificate, not a Lean declaration and not a counterexample to
the full paired Haar decoder.
"""

import json
from pathlib import Path
from flint import ctx, fmpq_series as Series


def main():
    data = json.loads(Path(__file__).with_name(
        "joint-family-biased-pool-germ.json").read_text())
    ctx.cap = 400
    zero, one, eps = Series([]), Series([1]), Series([0, 1])
    q = 1 << data["d"]
    gaps = [eps ** (1 << k) for k in range(data["d"])]
    poles = [sum((gaps[k] for k in range(data["d"])
                  if i >> k & 1), zero) for i in range(q)]
    kernel = [[one / (one - poles[i] - poles[j]) ** 2
               for j in range(q)] for i in range(q)]
    rows = []
    for word, a, b in data["queries"]:
        signs = data["sigma"] if word == 0 else data["tau"]
        assert signs[a] == 1 and signs[b] == -1
        rows.append([(kernel[a][j] - kernel[b][j]) * signs[j]
                     for j in range(q)])
    assert len(rows) == q + 1
    # The exact rational-function weights satisfy sum_i weight_i rows_i = 0.
    # Scaling the prescribed final weight by eps^100 avoids negative powers
    # in the formal power series implementation.
    mat = [[rows[j][i] for j in range(q)] + [-rows[-1][i] * eps ** 100]
           for i in range(q)]
    permutation, pivots = list(range(q)), []
    for k in range(q):
        valuation, i, j = min(
            (mat[i][j].valuation(), i, j)
            for i in range(k, q) for j in range(k, q)
            if mat[i][j].valuation() >= 0)
        assert min(a.prec for row in mat for a in row) > valuation
        pivots.append([valuation, str(mat[i][j][valuation])])
        mat[k], mat[i] = mat[i], mat[k]
        for row in mat:
            row[k], row[j] = row[j], row[k]
        permutation[k], permutation[j] = permutation[j], permutation[k]
        pivot = mat[k][k]
        mat[k] = [a / pivot for a in mat[k]]
        for i in range(q):
            if i == k:
                continue
            coefficient = mat[i][k]
            if coefficient.valuation() >= 0:
                mat[i] = [a - coefficient * b
                          for a, b in zip(mat[i], mat[k])]
    weights = [zero] * q + [eps ** 100]
    for k in range(q):
        weights[permutation[k]] = mat[k][-1]
    leading = [[a.valuation(), str(a[a.valuation()])] for a in weights]
    assert pivots == data["pivots"]
    assert leading == data["leading"]
    assert all(a[a.valuation()] > 0 for a in weights)
    assert min(a.prec for a in weights) == data["precision"]
    # Every residual vanishes to the available precision.  Exact vanishing
    # follows from the defining nonsingular rational-function linear system.
    for j in range(q):
        residual = sum((weights[i] * rows[i][j] for i in range(q + 1)), zero)
        assert residual.valuation() == -1
    print("PASS: 9 positive rational-function dual weights; precision",
          data["precision"])


if __name__ == "__main__":
    main()
