"""Exact small certificate for a nonzero Boolean moment rank plateau.

This uses rational symbolic arithmetic. It is a finite computation, separate
from the Lean proofs of the vanishing and nonvanishing moment identities.
"""

import json
import sympy as sp

points = [(1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 1), (3, 3)]
weights = sp.Matrix([1, -4, 3, 4, -4, -1, 1])
quadratic = sp.Matrix(
    [[1 for a, b in points], [a for a, b in points], [b for a, b in points],
     [a * a for a, b in points], [a * b for a, b in points],
     [b * b for a, b in points]]
)


def moment_matrix(order):
    return sp.Matrix([[1] * len(points)] + [
        [(a * x + b * y) ** q for a, b in points]
        for q in range(1, order + 1)
        for x, y in [(1, 0), (0, 1), (1, 1)]
    ])


minors = [int(quadratic[:, [i for i in range(7) if i != j]].det())
          for j in range(7)]
ranks = {str(q): moment_matrix(q).rank() for q in range(1, 5)}
moments = {
    str(q): [int(sum(weights[h] * (a * x + b * y) ** q
                    for h, (a, b) in enumerate(points)))
             for x, y in [(0, 0), (1, 0), (0, 1), (1, 1)]]
    for q in range(5)
}
assert all(minors)
assert quadratic * weights == sp.zeros(6, 1)
assert moment_matrix(3) * weights == sp.zeros(10, 1)
assert ranks["2"] == ranks["3"] == 6
assert ranks["4"] == 7
assert moments["4"] == [0, 0, 0, 24]
print(json.dumps({
    "points": points,
    "weights": list(map(int, weights)),
    "quadratic_deletion_determinants": minors,
    "moment_matrix_ranks": ranks,
    "moments_at_00_10_01_11": moments,
    "status": "exact rational finite computation",
}, indent=2))
