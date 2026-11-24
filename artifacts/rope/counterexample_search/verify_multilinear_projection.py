"""Exact pure-head top-degree matrix relaxation, for three or four heads."""
import argparse
from fractions import Fraction as Q
from itertools import permutations, product
import json
from pathlib import Path


def top_matrix(b, s, k, constant, groups):
    heads = len(b)
    rows, columns = groups[0], list(product(*groups[1:]))
    result = []
    for i in rows:
        row = []
        for column in columns:
            axes = (i,) + column
            value = constant * sum(
                product_q(b[h][axes[p[h]]] for h in range(heads))
                for p in permutations(range(heads)))
            for h in range(heads):
                others = [g for g in range(heads) if g != h]
                for axis in axes:
                    other_axes = [j for j in axes if j != axis]
                    value += k[h] * s[h][axis] * sum(
                        product_q(b[g][j] for g, j in zip(others, order))
                        for order in permutations(other_axes))
            row.append(value)
        result.append(row)
    return result


def product_q(values):
    result = Q(1)
    for value in values:
        result *= value
    return result


def verify(record):
    b, s = [[[Q(x) for x in row] for row in record[key]]
            for key in ['centered_bias', 'centered_mass']]
    k, constant = list(map(Q, record['token_half_difference'])), Q(record['readout_constant'])
    heads, n = len(b), record['n']
    assert heads in (3, 4) and len(s) == len(k) == len(record['atoms']) == heads
    assert all(len(row) == n for row in b + s)
    assert sorted(j for group in record['groups'] for j in group) == list(range(n))
    assert all(s[h][i] > abs(b[h][i]) for h in range(heads) for i in range(n))
    assert all(sum(row) < 1 for row in s)
    for h, atom in enumerate(record['atoms']):
        a, z = [list(map(Q, atom[name])) for name in ['a', 'b']]
        gamma, eta, v0, v1 = [Q(atom[name]) for name in ['gamma', 'eta', 'v0', 'v1']]
        assert min(a + z + [gamma]) > 0
        assert a == [s[h][i] - b[h][i] for i in range(n)]
        assert z == [s[h][i] + b[h][i] for i in range(n)]
        assert gamma == 1 - sum(s[h]) and eta == -k[h] * sum(b[h])
        assert v0 == -k[h] and v1 == k[h]
    c = top_matrix(b, s, k, constant, record['groups'])
    m = len(c)
    assert all(len(row) == m for row in c)
    negative = min(-c[i][j] for i in range(m) for j in range(m) if i != j)
    positive = min(sum(c[i][j] for i in range(m)) for j in range(m))
    assert negative > 0 and positive > 0
    assert [[str(x) for x in row] for row in c] == record['top_degree_matrix']
    return {'heads': heads, 'matrix_size': m,
            'minimum_negative_off_diagonal_margin': str(negative),
            'minimum_positive_column_sum': str(positive),
            'minimum_mass_slack': str(min(s[h][i] - abs(b[h][i])
                                        for h in range(heads) for i in range(n))),
            'minimum_query_weight': str(min(1 - sum(row) for row in s)),
            'status': 'exact coefficient relaxation only; Boolean witnesses unproved'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('files', nargs='+', type=Path)
    for path in parser.parse_args().files:
        print(json.dumps({'file': str(path), **verify(json.loads(path.read_text()))}, sort_keys=True))
