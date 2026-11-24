"""Exact checks for odd-positive-kernel-normalization.tex; not a universality test."""
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), Q(0))


def normalized(atom):
    eta, delta, gamma, alpha, rho, m = atom
    d = gamma + (alpha + 1) * sum(rho) / 2
    v = [r * (alpha - 1) / (2 * d) for r in rho]
    a = [r * ((alpha - 1) * z + alpha * delta) / (2 * d)
         for r, z in zip(rho, m)]
    a0 = (eta + dot(rho, m)) / d + sum(a)
    u = [z - a0 * q for z, q in zip(a, v)]
    w = list(map(abs, v))
    assert sum(w) < 1
    return a0, a, v, u, w


def evaluate(atom, t):
    eta, delta, gamma, alpha, rho, m = atom
    x = [(q + 1) // 2 for q in t]
    weights = [r * (alpha if b else 1) for r, b in zip(rho, x)]
    return (eta + sum(s * (z + delta * b)
                      for s, z, b in zip(weights, m, x))) / (gamma + sum(weights))


atoms = [
    (Q(2), Q(-3), Q(5), alpha,
     [Q(2), Q(3), Q(7)], [Q(1), Q(-2), Q(4)])
    for alpha in [Q(3), Q(2, 5), Q(1)]
]
cube = list(product([-1, 1], repeat=3))
for atom in atoms:
    a0, a, v, u, w = normalized(atom)
    for t in cube:
        value = evaluate(atom, t)
        opposite = evaluate(atom, [-q for q in t])
        assert value == (a0 + dot(a, t)) / (1 + dot(v, t))
        assert (value - opposite) / 2 == dot(u, t) / (1 - dot(w, t) ** 2)
        assert 1 - dot(w, t) ** 2 > 0

w = [Q(1, 4)] * 3
gram = [[sum(Q(t[i] * t[j], 8) / (1 - dot(w, t) ** 2) for t in cube)
         for j in range(3)] for i in range(3)]
assert all(gram[i][i] == Q(48, 35) for i in range(3))
assert all(gram[i][j] == Q(32, 105) for i in range(3) for j in range(3) if i != j)
for t in cube:
    score = Q(t[0]) / (1 - dot(w, t) ** 2) - Q(48, 35) * t[0] - Q(32, 105) * (t[1] + t[2])
    assert score == Q(32, 105) * t[0] * t[1] * t[2]

# Balanced-layer uniform shift, including mixed-sign direction vectors.
balanced = [t for t in product([-1, 1], repeat=4) if sum(t) == 0]
v = [Q(-3), Q(2), Q(5), Q(-1)]
epsilon = Q(1, 1000)
shifted = [Q(1, 8) + epsilon * q for q in v]
assert min(shifted) > 0 and sum(shifted) < 1
for t in balanced:
    assert dot(shifted, t) == epsilon * dot(v, t)

# Polynomial equality by exact coefficient expansion, H=1,...,7.
def multiply_polynomial(a, b):
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c


pencil_sizes = list(range(1, 8))
for size in pencil_sizes:
    lambdas = [Q((h + 1) ** 2) for h in range(size)]
    result = [Q(0)] * size
    for h, value in enumerate(lambdas):
        coefficient = Q(1)
        polynomial = [Q(1)]
        for k, other in enumerate(lambdas):
            if k != h:
                coefficient /= value - other
                polynomial = multiply_polynomial(polynomial, [Q(1), -other])
        result = [x + coefficient * y for x, y in zip(result, polynomial)]
    assert result == [Q(0)] * (size - 1) + [Q(1)]

report = {
    "status": "exact rational identity checks; not Lean and not a new asymptotic bound",
    "atom_orientations_checked": ["alpha>1", "0<alpha<1", "alpha=1"],
    "atom_vertex_checks": len(atoms) * len(cube),
    "three_bit_gram_matrix": [[str(x) for x in row] for row in gram],
    "parity_coefficient_after_first_level_cancellation": str(Q(32, 105)),
    "parity_vertex_checks": len(cube),
    "balanced_layer_shift_checks": len(balanced),
    "common_direction_polynomial_identity_sizes": pencil_sizes,
}
Path(__file__).with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
