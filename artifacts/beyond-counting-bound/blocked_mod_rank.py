"""Memory-bounded exact modular elimination for the jet experiment.

Entries are stored as uint16. Panel operations use int64. Block products use
binary64 only when every integer product and every possible partial sum is
below 2**53, then convert back to int64 before modular reduction. Thus no
floating rank threshold is used. Run sustained calculations through heavy.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

import numpy as np


def integer_product(left, right, prime):
    assert left.shape[1] * (prime - 1) ** 2 < 2**53
    return (left.astype(np.float64) @ right.astype(np.float64)).astype(np.int64)


def blocked_rank(a, prime, deadline, panel_width=64, row_chunk=256, progress=None):
    assert a.dtype == np.uint16 and prime < 2**16
    assert panel_width * (prime - 1) ** 2 < 2**53
    rows, cols = a.shape
    rank, det, swaps = 0, 1, 0
    pivots = []
    for first in range(0, cols, panel_width):
        if time.monotonic() >= deadline:
            return rank, pivots, None, False
        last = min(cols, first + panel_width)
        panel = a[rank:, first:last].astype(np.int64)
        lower = np.zeros((rows - rank, last - first), dtype=np.int64)
        diagonal = []
        found = 0
        for column in range(last - first):
            nonzero = np.flatnonzero(panel[found:, column])
            if not len(nonzero):
                continue
            pivot = found + int(nonzero[0])
            if pivot != found:
                panel[[found, pivot]] = panel[[pivot, found]]
                lower[[found, pivot]] = lower[[pivot, found]]
                a[[rank + found, rank + pivot]] = a[[rank + pivot, rank + found]]
                swaps += 1
            value = int(panel[found, column])
            diagonal.append(value)
            det = det * value % prime
            inverse = pow(value, -1, prime)
            panel[found] = panel[found] * inverse % prime
            factors = panel[found + 1:, column].copy()
            lower[found + 1:, found] = factors
            panel[found + 1:] = (panel[found + 1:] - factors[:, None] * panel[found]) % prime
            pivots.append(first + column)
            found += 1
            if rank + found == rows:
                break
        a[rank:, first:last] = panel.astype(np.uint16)
        if found and last < cols:
            upper = np.empty((found, cols - last), dtype=np.int64)
            for i, value in enumerate(diagonal):
                row = a[rank + i, last:].astype(np.int64)
                if i:
                    row -= integer_product(lower[i:i + 1, :i], upper[:i], prime)[0]
                upper[i] = (row % prime) * pow(value, -1, prime) % prime
            a[rank:rank + found, last:] = upper.astype(np.uint16)
            for start in range(found, rows - rank, row_chunk):
                stop = min(rows - rank, start + row_chunk)
                product = integer_product(lower[start:stop, :found], upper, prime)
                residue = (a[rank + start:rank + stop, last:].astype(np.int64) - product) % prime
                a[rank + start:rank + stop, last:] = residue.astype(np.uint16)
        rank += found
        if progress:
            progress(rank, last, rows, cols)
        if rank == rows:
            return rank, pivots, det * (-1 if swaps % 2 else 1) % prime, True
    return rank, pivots, None, True


def self_check():
    from test_reciprocal_jet_rank import rank_mod
    rng = np.random.default_rng(812754)
    cases = 0
    for prime in [3, 101, 65521]:
        for rows, cols in [(1, 1), (5, 13), (13, 5), (37, 61), (70, 80)]:
            for deficient in [False, True]:
                a = rng.integers(0, prime, size=(rows, cols), dtype=np.int64)
                if deficient:
                    a[:, 0] = 0
                    if rows > 2:
                        a[-1] = a[0]
                        a[-2] = (a[0] + a[1]) % prime
                expected, _, _ = rank_mod(a, prime, float('inf'))
                for width in [1, 4, 17, 64]:
                    actual, pivots, determinant, complete = blocked_rank(
                        a.astype(np.uint16), prime, float('inf'), width, 11)
                    assert complete and actual == expected, (prime, a.shape, width, expected, actual)
                    if actual == rows:
                        # Independent scalar elimination for the claimed pivot minor.
                        b = a[:, pivots].copy()
                        reference = 1
                        for i in range(rows):
                            j = i + int(np.flatnonzero(b[i:, i])[0])
                            if i != j:
                                b[[i, j]] = b[[j, i]]
                                reference = -reference
                            value = int(b[i, i]); reference = reference * value % prime
                            for k in range(i + 1, rows):
                                b[k, i:] = (b[k, i:] - int(b[k, i]) * pow(value, -1, prime) * b[i, i:]) % prime
                        assert determinant == reference, (determinant, reference)
                    cases += 1
    return cases


def jet_matrix(d, q, prime):
    count = 1 << d
    indices = np.arange(count, dtype=np.int64)
    subsets = [()] + [(i,) for i in range(d)] + list(itertools.combinations(range(d), 2))
    assert count + q < prime
    inverse_cubes = np.array([0] + [pow(v, -3, prime) for v in range(1, count + q + 1)], dtype=np.uint16)
    matrix = np.empty((q * len(subsets), count), dtype=np.uint16)
    for j in range(q):
        values = inverse_cubes[indices + j + 2]
        for k, subset in enumerate(subsets):
            mask = np.ones(count, dtype=bool)
            for i in subset:
                mask &= ((indices >> i) & 1).astype(bool)
            matrix[j * len(subsets) + k] = np.where(mask, values, 0)
    return matrix


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    parser.add_argument('--dimensions', default='14,15')
    parser.add_argument('--seconds', type=float, default=12600)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    print(json.dumps({'event': 'self_check', 'cases': self_check()}), flush=True)
    if args.check_only:
        return
    assert args.output
    args.output.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + args.seconds
    prime = 65521
    with (args.output / 'results.jsonl').open('a', buffering=1) as log:
        for d in map(int, args.dimensions.split(',')):
            if time.monotonic() >= deadline:
                break
            length = 1 + d + d * (d - 1) // 2
            q = (1 << d) // length
            started = time.monotonic()
            matrix = jet_matrix(d, q, prime)
            print(json.dumps({'event': 'matrix', 'd': d, 'shape': matrix.shape, 'bytes': matrix.nbytes}), flush=True)
            last_report = started
            def progress(rank, column, rows, cols):
                nonlocal last_report
                now = time.monotonic()
                if now - last_report >= 50:
                    print(json.dumps({'event': 'rank_progress', 'd': d, 'rank': rank, 'column': column,
                                      'rows': rows, 'elapsed_seconds': now - started}), flush=True)
                    last_report = now
            rank, pivots, determinant, complete = blocked_rank(matrix, prime, deadline, progress=progress)
            record = {'d': d, 'q': q, 'rows': matrix.shape[0], 'columns': matrix.shape[1],
                      'prime': prime, 'beta': [1 << i for i in range(d)], 'r': list(range(2, q + 2)),
                      'rank': rank, 'elimination_complete': complete, 'full_row_rank': rank == matrix.shape[0],
                      'pivot_columns': pivots, 'pivot_minor_determinant': determinant,
                      'elapsed_seconds': time.monotonic() - started,
                      'interpretation': 'auxiliary finite-field rank only; no head lower bound'}
            log.write(json.dumps(record) + '\n')
            print(json.dumps({k: v for k, v in record.items() if k not in ['pivot_columns', 'r', 'beta']}), flush=True)
            del matrix


if __name__ == '__main__':
    main()
