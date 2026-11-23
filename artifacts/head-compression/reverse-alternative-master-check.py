"""Exact limiting checks for the signed-master-function construction."""

from fractions import Fraction as Q
from itertools import product


def multiply(values):
    result = Q(1)
    for value in values:
        result *= value
    return result


offsets = tuple(range(1, 5))
roots = tuple(range(1, 4))
residues = tuple(
    multiply(-beta - root for root in roots)
    / multiply(other - beta for other in offsets if other != beta)
    for beta in offsets
)
assert residues == (Q(-4), Q(30), Q(-60), Q(35))

second = {}
for root in roots:
    first_derivative = sum(a / (root + beta) for a, beta in zip(residues, offsets))
    second[root] = -sum(a / (root + beta) ** 2 for a, beta in zip(residues, offsets))
    expected = multiply(root - other for other in roots if other != root)
    expected /= multiply(root + beta for beta in offsets)
    assert first_derivative == 0
    assert second[root] == expected != 0

# Address saddle at c=(1,2).
gradient = (Q(1, 4) - Q(1, 2) / 2, Q(1, 4) - Q(3, 4) / 3)
hessian = ((Q(1, 16), Q(-1, 16)), (Q(-1, 16), Q(1, 48)))
assert gradient == (0, 0)
address_det = hessian[0][0] * hessian[1][1] - hessian[0][1] * hessian[1][0]
assert address_det == Q(-1, 384)

for signal_roots in product(roots, repeat=2):
    determinant = multiply(second[root] for root in signal_roots) * address_det
    assert determinant != 0

# Exact termwise elliptic identity at a generic rational positive c.
c = (Q(2, 3), Q(5, 4), Q(7, 6))
for x in product((0, 1), repeat=len(c)):
    dot = sum(ci * xi for ci, xi in zip(c, x))
    boolean_quadratic = sum(ci * xi * xi for ci, xi in zip(c, x)) + dot * dot
    assert boolean_quadratic == dot * (1 + dot)

print("PASS: exact residues, three simple signal roots, nine nonsingular limiting points,")
print("      address saddle determinant -1/384, and Boolean elliptic identity.")
