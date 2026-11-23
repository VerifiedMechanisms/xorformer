"""Exact certificate: same denominator orders, different full-cube sign classes."""

from fractions import Fraction as Q
from itertools import product


def determinant(matrix):
    a = [[Q(z) for z in row] for row in matrix]
    result = Q(1)
    for k in range(len(a)):
        j = next((j for j in range(k, len(a)) if a[j][k]), None)
        if j is None:
            return Q(0)
        if j != k:
            a[k], a[j] = a[j], a[k]
            result = -result
        pivot = a[k][k]
        result *= pivot
        for j in range(k + 1, len(a)):
            ratio = a[j][k] / pivot
            for ell in range(k + 1, len(a)):
                a[j][ell] -= ratio * a[k][ell]
    return result


vertices = list(product((0, 1), repeat=4))
weights = [1, 3, 9, 27]
vs = ([8, -9, 1, 4], [2, -8, -6, -1])
rows = [0, 1, 3, 6, 8, 9, 10, 12, 13, 14]
circuits = [
    [5759190, -584406, 319176, -92718, 334041, 33920,
     -259736, 1076448, 111568, -553363],
    [143600853, -7864640, 2272334, -574407, -19849030,
     5150082, -10647419, -3965287, -413088, 2893753],
]
scales = [5600, 400]
coefficients = [726397, 413029720, 1022839140, 2018070760, 6209249130,
                -43229541511, -100481986842, -202681766582, -623851360053]
expected_signs = [1, -1, 1, 1, -1, -1, -1, -1,
                  -1, 1, -1, -1, -1, -1, 1, -1]
orders = []
matrices = []
for v, lam, scale in zip(vs, circuits, scales):
    b_values, c_values, matrix = [], [], []
    assert all(100 * w + delta > 0 for w, delta in zip(weights, v))
    for x in vertices:
        b = 1 + sum(w * t for w, t in zip(weights, x))
        c = 100 * b + sum(delta * t for delta, t in zip(v, x))
        assert 0 < b < 100 <= c
        b_values.append(b)
        c_values.append(c)
        matrix.append([b * c] + [t * c for t in x] + [t * b for t in x])
    assert len(set(b_values)) == len(set(c_values)) == 16
    order_b = sorted(range(16), key=b_values.__getitem__)
    order_c = sorted(range(16), key=c_values.__getitem__)
    assert order_b == order_c
    orders.append(order_b)
    restricted = [matrix[j] for j in rows]
    cofactors = [(-1) ** j * determinant(restricted[:j] + restricted[j + 1:])
                 for j in range(10)]
    assert cofactors == [scale * t for t in lam]
    assert all(t != 0 for t in cofactors)
    assert all(sum(lam[j] * restricted[j][k] for j in range(10)) == 0
               for k in range(9))
    matrices.append(matrix)
assert orders[0] == orders[1]
values = [sum(c * entry for c, entry in zip(coefficients, row))
          for row in matrices[0]]
assert all(t != 0 for t in values)
signs = [1 if t > 0 else -1 for t in values]
assert signs == expected_signs
assert [signs[j] for j in rows] == [1 if t > 0 else -1 for t in circuits[1]]
print("PASS: strict cube admissibility; identical orders; all exact nonzero cofactors;")
print("      explicit full-cube strict witness; dual certificate excludes second pair")
