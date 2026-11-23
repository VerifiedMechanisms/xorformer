"""Exact checks for a full-cube three-pole identity and a regularity certificate.

This proves no asymptotic complexity bound.  All computations use rational
arithmetic or a finite field; there are no numerical optimization claims.
"""

from fractions import Fraction
from itertools import product


def denominators(x):
    d = 100 + sum((i + 4) * xi for i, xi in enumerate(x))
    a, b = x[0] - x[1], x[1] - x[2]
    return [d + 2 * a + 2 * b, d + a, d + b], [d + 2 * a + b, d + a + 2 * b, d]


def determinant_mod(matrix, prime):
    matrix = [row[:] for row in matrix]
    result = 1
    for j in range(len(matrix)):
        pivot = next((i for i in range(j, len(matrix)) if matrix[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            result = -result
        value = matrix[j][j]
        result = result * value % prime
        inverse = pow(value, -1, prime)
        for i in range(j + 1, len(matrix)):
            factor = matrix[i][j] * inverse % prime
            matrix[i] = [(v - factor * w) % prime for v, w in zip(matrix[i], matrix[j])]
    return result % prime


for dimension in range(3, 7):
    for vertex in product([0, 1], repeat=dimension):
        left, right = denominators(vertex)
        assert min(left + right) > 0
        assert sum(Fraction(1, d) for d in left) == sum(Fraction(1, d) for d in right)
    print(f"Full-cube identity, dimension {dimension}: exact pass")

prime = 1_000_003
# Trial division verifies primality rather than treating it as an assumption.
assert all(prime % d for d in range(2, 1001))
selected = [0, 16, 8, 4, 3, 5, 6, 17, 9, 12, 10, 11, 2, 18, 14, 15, 7, 13]
vertices = list(product([0, 1], repeat=5))
jacobians = [[], []]
for index in selected:
    x = vertices[index]
    for side, ds in enumerate(denominators(x)):
        # Parameters are all six affine coefficients of each denominator.
        row = [(-v * pow(d * d, -1, prime)) % prime for d in ds for v in (1,) + x]
        jacobians[side].append(row)
determinants = [determinant_mod(j, prime) for j in jacobians]
assert determinants == [2363, 997640]
assert all(determinants)
print(f"Selected lexicographic vertex indices: {selected}")
print(f"Jacobian determinants modulo {prime}: {determinants}")
print("Both 18-parameter maps have full real column rank at these exact points.")
