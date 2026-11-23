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


def determinant(matrix):
    matrix = [list(map(Q, row)) for row in matrix]
    value = Q(1)
    for column in range(len(matrix)):
        pivot = next((i for i in range(column, len(matrix)) if matrix[i][column]), None)
        if pivot is None:
            return Q(0)
        if pivot != column:
            matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
            value = -value
        pivot_value = matrix[column][column]
        value *= pivot_value
        for i in range(column + 1, len(matrix)):
            ratio = matrix[i][column] / pivot_value
            for j in range(column + 1, len(matrix)):
                matrix[i][j] -= ratio * matrix[column][j]
    return value


# A corank-one critical point and a regular nonconstant normal contact.
weights = {
    (0, 0, 0): 3, (1, 0, 0): 12, (0, 1, 0): -12, (0, 0, 1): -12,
    (1, 1, 0): -9, (1, 0, 1): -9, (0, 1, 1): 27, (1, 1, 1): 0,
}
kernel = (2, 1, 1)
gradient = [Q(0) for _ in kernel]
normal_hessian = [[Q(0) for _ in kernel] for _ in kernel]
third_contraction = [[Q(0) for _ in kernel] for _ in kernel]
assert sum(weights.values()) == 0
assert sum(Q(weight, 1 + sum(x)) for x, weight in weights.items()) == 0
for x, weight in weights.items():
    denominator = 1 + sum(x)
    numerator = sum(v * xi for v, xi in zip(kernel, x))
    for i in range(3):
        gradient[i] += Q(weight * x[i], denominator)
        for j in range(3):
            normal_hessian[i][j] -= Q(weight * x[i] * x[j], denominator ** 2)
            third_contraction[i][j] += Q(2 * weight * numerator * x[i] * x[j], denominator ** 3)
assert gradient == [0, 0, 0]
assert normal_hessian == [[-1, 1, 1], [1, 1, -3], [1, -3, 1]]
assert third_contraction == [[2, -2, -2], [-2, -1, 4], [-2, 4, -1]]
for i in range(3):
    assert sum(normal_hessian[i][j] * kernel[j] for j in range(3)) == 0
    assert normal_hessian[i][i] + sum(normal_hessian[i]) == 0
assert sum(kernel[i] * third_contraction[i][j] * kernel[j]
           for i in range(3) for j in range(3)) == -2
contact_hessian = [[Q(0) for _ in range(5)] for _ in range(5)]
for i in range(2):
    for j in range(3):
        contact_hessian[i][2 + j] = contact_hessian[2 + j][i] = normal_hessian[1 + i][j]
for i in range(3):
    for j in range(3):
        contact_hessian[2 + i][2 + j] = third_contraction[i][j]
assert determinant(contact_hessian) == -32

print("PASS: exact residues, three simple signal roots, nine nonsingular limiting points,")
print("      address saddle determinant -1/384, and Boolean elliptic identity.")
print("PASS: full Boolean Hessian identity, corank-one contact, third derivative -2,")
print("      and nondegenerate five-parameter contact Hessian determinant -32.")
