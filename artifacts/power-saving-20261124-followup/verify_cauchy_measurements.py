"""Exact finite checks for the four-bit linear-measurement obstruction."""

from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path


def mul_poly(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def prod_poly(factors):
    out = [Q(1)]
    for f in factors:
        out = mul_poly(out, f)
    return out


residues = [-4, 30, -60, 35]
rhs = prod_poly([[-r, 1] for r in [1, 2, 3]])
lhs = [Q(0)] * 4
for t, c in enumerate(residues, 1):
    p = prod_poly([[u, 1] for u in range(1, 5) if u != t])
    lhs = [a + c * b for a, b in zip(lhs, p)]
assert lhs == rhs


def measurement(s):
    return sum(Q(c, s + t) for t, c in enumerate(residues, 1))


def derivative(s):
    return sum(-Q(c, (s + t) ** 2) for t, c in enumerate(residues, 1))


rows = []
tables = set()
for b1, b2 in product([1, 2, 3], repeat=2):
    weights = [1, 2, b1, b2]
    total = sum(weights)
    alpha, gamma, eta = 1 + 2 * total, Q(1, 2), Q(1)
    rho = [Q(w, 2 * total) for w in weights]
    table = []
    for bits in product([0, 1], repeat=4):
        den = 1 + sum(w * x for w, x in zip(weights, bits))
        value = Q(1, den)
        atom_den = gamma + sum(r * (alpha if x else 1) for r, x in zip(rho, bits))
        atom_num = eta
        assert atom_num / atom_den == value > 0
        table.append(value)
    tables.add(tuple(table))
    assert measurement(b1) == measurement(b2) == 0
    jac = derivative(b1) * derivative(b2)
    assert jac != 0
    rows.append({"b": [b1, b2], "jacobian_determinant": str(jac),
                 "table": [str(x) for x in table]})
assert len(tables) == 9
assert [derivative(r) for r in [1, 2, 3]] == [Q(1, 60), -Q(1, 360), Q(1, 420)]
report = {"arithmetic": "exact fractions.Fraction", "positive_regular_branches": 9,
          "all_truth_tables": "constant true", "residues": residues,
          "polynomial_identity_coefficients": [str(x) for x in lhs], "branches": rows}
output = Path(__file__).with_name("cauchy_measurement_certificate.json")
output.write_text(json.dumps(report, indent=2) + "\n")
print("Verified 9 distinct positive single-head tables, all measurements zero, all Jacobians nonzero.")
