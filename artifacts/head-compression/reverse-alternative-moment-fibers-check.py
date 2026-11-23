"""Exact sanity checks for the written Stieltjes moment-fiber argument."""

from fractions import Fraction as Q
from itertools import product


def determinant(matrix):
    a = [[Q(t) for t in row] for row in matrix]
    value = Q(1)
    for k in range(len(a)):
        pivot_row = next((j for j in range(k, len(a)) if a[j][k]), None)
        if pivot_row is None:
            return Q(0)
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            value = -value
        pivot = a[k][k]
        value *= pivot
        for j in range(k + 1, len(a)):
            ratio = a[j][k] / pivot
            for ell in range(k + 1, len(a)):
                a[j][ell] -= ratio * a[k][ell]
    return value


count = 0
for h in range(2, 9):
    atoms = range(1, h + 1)
    for k in range(1, h):
        poles = range(h + 2, h + 2 + h - k)
        jacobian = [[j * atom ** (j - 1) for atom in atoms]
                    for j in range(1, k + 1)]
        jacobian += [[Q(1, (pole - atom) ** 2) for atom in atoms]
                     for pole in poles]
        assert determinant(jacobian) != 0
        count += 1

u = [Q(1, 2), Q(7, 2), Q(11, 2)]
w = [Q(5, 2), Q(1, 2), Q(7, 2)]
shift = w[1:] + w[:1]
assert [a + b for a, b in zip(u, w)] == [3, 4, 9]
assert [a + b for a, b in zip(u, shift)] == [1, 7, 8]
assert sum(a + b for a, b in zip(u, w)) == sum(a + b for a, b in zip(u, shift))
for x1, x2, y in product((0, 1), repeat=3):
    pole = 20 - 10 * y
    left = [pole - a * x1 - b * x2 for a, b in zip(u, w)]
    right = [pole - a * x1 - b * x2 for a, b in zip(u, shift)]
    assert min(left + right) > 0
    score = sum((1 / den for den in left), Q(0)) - sum((1 / den for den in right), Q(0))
    if x1 == 0 or x2 == 0:
        assert score == 0
    elif y == 0:
        assert score == -Q(1453, 2217072)
    else:
        assert score == Q(23, 63)

print(f"PASS: {count} exact moment/readout Jacobians; three-coordinate cube")
print("      denominator positivity, exact axis zeros, opposite mixed-face signs")
