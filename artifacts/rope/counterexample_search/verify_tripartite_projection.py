"""Verify an exact pure-three cubic coefficient relaxation.

The certificate has an inverse-positive 6 by 6 tripartite coefficient matrix.
It does not certify the required Boolean parity-face witnesses.
"""
from fractions import Fraction as Q
from itertools import permutations, product
import argparse
import json
from pathlib import Path


def cross_coefficients(b, s, k, constant):
    matrix = []
    for i in range(6):
        row = []
        for j, z in product(range(6, 8), range(8, 11)):
            axes = [i, j, z]
            value = constant * sum(
                b[0][axes[p[0]]] * b[1][axes[p[1]]] * b[2][axes[p[2]]]
                for p in permutations(range(3)))
            for h in range(3):
                p, q = [other for other in range(3) if other != h]
                for v in axes:
                    w, u = [axis for axis in axes if axis != v]
                    value += k[h] * s[h][v] * (b[p][w] * b[q][u] + b[p][u] * b[q][w])
            row.append(value)
        matrix.append(row)
    return matrix


def verify(record):
    b = [[Q(x) for x in row] for row in record['centered_bias']]
    s = [[Q(x) for x in row] for row in record['centered_mass']]
    k = list(map(Q, record['token_half_difference']))
    constant = Q(record['readout_constant'])
    assert len(b) == len(s) == len(k) == 3
    assert all(len(row) == 11 for row in b + s)
    assert all(s[h][i] > abs(b[h][i]) for h in range(3) for i in range(11))
    assert all(sum(row) < 1 for row in s)
    for h, atom in enumerate(record['atoms']):
        a, z = [list(map(Q, atom[name])) for name in ['a', 'b']]
        gamma, eta, v0, v1 = [Q(atom[name]) for name in ['gamma', 'eta', 'v0', 'v1']]
        assert min(a + z + [gamma]) > 0
        assert all(a[i] == s[h][i] - b[h][i] and z[i] == s[h][i] + b[h][i]
                   for i in range(11))
        assert gamma == 1 - sum(s[h]) and v0 == -k[h] and v1 == k[h]
        assert eta == -k[h] * sum(b[h])
        # The atom numerator is k_h * sum_i s_hi*z_i with zero constant.
        assert eta + sum((v0 * a[i] + v1 * z[i]) / 2 for i in range(11)) == 0
        assert all((v1 * z[i] - v0 * a[i]) / 2 == k[h] * s[h][i] for i in range(11))
    c = cross_coefficients(b, s, k, constant)
    off_margin = min(-c[i][j] for i in range(6) for j in range(6) if i != j)
    column_margin = min(sum(c[i][j] for i in range(6)) for j in range(6))
    assert off_margin > 0 and column_margin > 0
    assert [[str(x) for x in row] for row in c] == record['cubic_cross_matrix']
    return {'minimum_mass_slack': str(min(s[h][i] - abs(b[h][i])
                                        for h in range(3) for i in range(11))),
            'minimum_query_weight': str(min(1 - sum(row) for row in s)),
            'minimum_negative_off_diagonal_margin': str(off_margin),
            'minimum_positive_column_sum': str(column_margin),
            'status': 'exact coefficient relaxation only; Boolean witnesses unproved'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('files', nargs='*', type=Path)
    args = parser.parse_args()
    paths = args.files or [Path(__file__).with_name('exact_tripartite_projection.json')]
    for path in paths:
        print(json.dumps({'file': str(path), **verify(json.loads(path.read_text()))}, sort_keys=True))
