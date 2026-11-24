"""Exact rational check of a frozen-head interior-denominator obstruction.

No numerical optimization is used. This checks one auxiliary obstruction, not
an unrestricted head lower bound or a Lean theorem.
"""
from itertools import product
from pathlib import Path
import json
import sympy as q

vertices = list(product([0, 1], repeat=3))
X = q.Matrix([[1, *x] for x in vertices])
a = q.Matrix([-q.Rational(1, 2), 1, 1, 1])
b = q.Matrix([1, 1, 2, 3])
d = q.Matrix([-3, 2, 2, 2])
A, B, D = X * a, X * b, X * d
f = q.Matrix([(-1) ** (sum(x) + 1) for x in vertices])
base = q.diag(*f) * X.row_join(q.diag(*[-A[i] / B[i] for i in range(8)]) * X)
assert base[:7, :7].det() == q.Rational(3, 320)
assert base * a.col_join(b) == q.zeros(8, 1)
assert B.T * base == q.zeros(1, 8)

t = q.Rational(1, 10)
R = q.Matrix([(D[i] - A[i]) / (B[i] + t * D[i])
              - D[i] / (B[i] + t * (D[i] - A[i])) for i in range(8)])
score = q.Matrix([A[i] / B[i] + R[i] for i in range(8)])
for i in range(8):
    assert score[i] == t**2 * A[i] * D[i] * (D[i] - A[i]) / (
        B[i] * (B[i] + t * D[i]) * (B[i] + t * (D[i] - A[i])))
    assert f[i] * score[i] > 0
for coeffs in [b, b + t * d, b + t * (d - a)]:
    assert all(v > 0 for v in coeffs)
M = q.diag(*f) * X.row_join(q.diag(*R) * X)
inv = M.inv()
assert M * inv == q.eye(8)
Z = inv[4:8, :]
assert all(v > 0 for v in Z)
gamma = min(Z[j, k] / sum(Z[i, k] for i in range(4))
            for j in range(4) for k in range(8))
assert gamma > 0
out = {
    "status": "exact rational finite certificate; not Lean verification",
    "vertices": vertices,
    "t": str(t),
    "a_coefficients": [str(v) for v in a],
    "b_coefficients": [str(v) for v in b],
    "d_coefficients": [str(v) for v in d],
    "base_rank_seven_minor": str(base[:7, :7].det()),
    "residual": [str(v) for v in R],
    "strict_signed_scores": [str(f[i] * score[i]) for i in range(8)],
    "inverse_bottom_rows": [[str(Z[j, k]) for k in range(8)] for j in range(4)],
    "normalized_denominator_coefficient_lower_bound": str(gamma),
    "scope": "Heads two and three fixed; joint deformation remains possible.",
}
path = Path(__file__).with_name("frozen_head_boundary_exact.json")
path.write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({"certificate": str(path), "gamma": str(gamma), "checks": "passed"}))
