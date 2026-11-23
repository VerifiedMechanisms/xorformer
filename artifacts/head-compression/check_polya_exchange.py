"""Exact diagnostics for exchange averaging and finite-step rigidity.

The manual theorem is in polya-exchange-rigidity.tex. These checks do not
prove any universal upper or lower bound on Boolean head complexity.
Run through heavy, with python-flint available.
"""
import argparse
from fractions import Fraction as F
from itertools import combinations, product
import json
import random
import time

from flint import fmpq_mat, nmod_mat


def feature(b, x):
    return b[0] / (b[0] + sum(v * t for v, t in zip(b[1:], x)))


def column(b, edge, step, points):
    i, j = edge
    plus, minus = list(b), list(b)
    plus[i] += step
    plus[j] -= step
    minus[i] -= step
    minus[j] += step
    assert min(plus) > 0 and min(minus) > 0
    result = []
    for x in points:
        actual = feature(plus, x) + feature(minus, x) - 2 * feature(b, x)
        B = b[0] + sum(v * t for v, t in zip(b[1:], x))
        if i == 0:
            numerator = (b[0] - B) * (1 - x[j - 1])
        else:
            numerator = b[0] * (x[i - 1] - x[j - 1]) ** 2
        expected = 2 * step ** 2 * numerator / (B * (B ** 2 - step ** 2))
        assert actual == expected
        result.append(actual)
    return result


def rational_matrix(columns):
    return fmpq_mat([[str(v) for v in row] for row in zip(*columns)])


def null_vector(matrix):
    reduced, rank = matrix.rref()
    width = matrix.ncols()
    pivots = [next(j for j in range(width) if reduced[i, j]) for i in range(rank)]
    free = next(j for j in range(width) if j not in pivots)
    v = [F(0)] * width
    v[free] = F(1)
    for i, pivot in enumerate(pivots):
        v[pivot] = -F(str(reduced[i, free]))
    assert all(sum(F(str(matrix[i, j])) * v[j] for j in range(width)) == 0
               for i in range(matrix.nrows()))
    return v


def run():
    records = []
    rng = random.Random(2026112318)
    prime = 1000000007
    for n in range(1, 8):
        for mode in ('equal', 'distinct'):
            b = list(map(F, [3] * (n + 1) if mode == 'equal' else range(3, n + 4)))
            points = list(product((0, 1), repeat=n))
            edges = list(combinations(range(n + 1), 2))
            columns = [[column(b, edge, F(d), points) for edge in edges] for d in (1, 2)]
            common_ranks = []
            for cs in columns:
                assert all(sum(b[i] * b[j] * cs[e][x] for e, (i, j) in enumerate(edges)) == 0
                           for x in range(len(points)))
                rank = rational_matrix(cs).rref()[1]
                assert rank == len(edges) - 1
                common_ranks.append(rank)
            record = dict(n=n, mode=mode, b=list(map(str, b)), edges=len(edges),
                          exact_formula_and_averaging=True, common_ranks=common_ranks)
            if 2 <= n <= 5:
                masks = range(1, (1 << len(edges)) - 1)
                exhaustive = True
            elif n >= 6:
                masks = [rng.randrange(1, (1 << len(edges)) - 1) for _ in range(256)]
                exhaustive = False
            else:
                records.append(record)
                continue
            modular = [[[int(v.numerator % prime) * pow(v.denominator, -1, prime) % prime
                         for v in col] for col in cs] for cs in columns]
            checked, found = 0, None
            for mask in masks:
                cs = [modular[(mask >> e) & 1][e] for e in range(len(edges))]
                rank = nmod_mat(list(map(list, zip(*cs))), prime).rank()
                checked += 1
                if rank < len(edges):
                    exact = [columns[(mask >> e) & 1][e] for e in range(len(edges))]
                    mat = rational_matrix(exact)
                    exact_rank = mat.rref()[1]
                    if exact_rank < len(edges):
                        vector = null_vector(mat)
                        found = dict(mask=mask, rank=exact_rank,
                                     increments=[1 + ((mask >> e) & 1) for e in range(len(edges))],
                                     edge_list=edges, weights=list(map(str, vector)),
                                     exact_cube_vertices_checked=len(points))
                        assert n < 6, 'Counterexample to the manual two-magnitude theorem'
                        break
            record.update(mixed_patterns_checked=checked,
                          all_mixed_patterns_exhausted=exhaustive and found is None,
                          first_exact_mixed_relation=found,
                          modular_prime=prime)
            records.append(record)
            print(json.dumps({k: v for k, v in record.items() if k != 'first_exact_mixed_relation'}), flush=True)
    return records


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True)
    args = p.parse_args()
    started = time.monotonic()
    data = dict(scope='Finite diagnostics; universal target unproved.', cases=run(),
                elapsed_seconds=time.monotonic() - started)
    with open(args.out, 'w') as f:
        json.dump(data, f, indent=2)
        f.write('\n')
