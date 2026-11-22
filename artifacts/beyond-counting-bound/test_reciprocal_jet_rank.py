"""Exact finite-field ranks of Boolean reciprocal two-jet evaluations.

This tests an auxiliary interpolation mechanism, not a head lower bound.
Rank over a prime field certifies a nonzero rational minor at the same integer
parameters when no denominator vanishes modulo that prime.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

import numpy as np


def rank_mod(matrix, prime, deadline):
    a = np.array(matrix, dtype=np.int64, copy=True)
    rows, cols = a.shape
    rank = 0
    pivots = []
    for col in range(cols):
        if time.monotonic() >= deadline:
            return rank, pivots, False
        nz = np.flatnonzero(a[rank:, col])
        if not len(nz):
            continue
        pivot = rank + int(nz[0])
        a[[rank, pivot]] = a[[pivot, rank]]
        inv = pow(int(a[rank, col]), -1, prime)
        a[rank, col:] = a[rank, col:] * inv % prime
        for start in range(rank + 1, rows, 128):
            stop = min(rows, start + 128)
            factors = a[start:stop, col].copy()
            a[start:stop, col:] = (
                a[start:stop, col:] - factors[:, None] * a[rank, col:][None, :]
            ) % prime
        pivots.append(col)
        rank += 1
        if rank == rows:
            return rank, pivots, True
    return rank, pivots, True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=21600)
    ap.add_argument('--case-seconds', type=float, default=3600)
    ap.add_argument('--max-d', type=int, default=12)
    ap.add_argument('--min-d', type=int, default=4)
    ap.add_argument('--kinds', choices=['both', 'binary', 'random'], default='both')
    ap.add_argument('--q-mode', choices=['sweep', 'maximum'], default='sweep')
    ap.add_argument('--seed', type=int, default=911223)
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    prime = 65521
    deadline = time.monotonic() + args.seconds
    with (args.output / 'results.jsonl').open('a', buffering=1) as log:
        for d in range(args.min_d, args.max_d + 1):
            cube = ((np.arange(1 << d)[:, None] >> np.arange(d)) & 1).astype(np.int64)
            subsets = [()] + [(i,) for i in range(d)] + list(itertools.combinations(range(d), 2))
            u = np.array([np.prod(cube[:, s], axis=1) if s else np.ones(1 << d, dtype=np.int64)
                          for s in subsets], dtype=np.int64)
            qmax = (1 << d) // len(subsets)
            qs = [qmax] if args.q_mode == 'maximum' else sorted(set([1, 2, max(1, qmax // 2), qmax]))
            for q in qs:
                if q * len(subsets) > (1 << d) or time.monotonic() >= deadline:
                    continue
                kinds = ['binary', 'random'] if args.kinds == 'both' else [args.kinds]
                for kind in kinds:
                    beta = 2 ** np.arange(d) if kind == 'binary' else rng.integers(1, 100, size=d)
                    c = cube @ beta
                    r = np.arange(2, 2 + q, dtype=np.int64)
                    denom = (r[:, None] + c[None, :]) % prime
                    assert np.all(denom)
                    inverse = np.array([pow(int(v), -3, prime) for v in denom.ravel()], dtype=np.int64).reshape(q, -1)
                    matrix = (inverse[:, None, :] * u[None, :, :]) % prime
                    matrix = matrix.reshape(q * len(subsets), -1)
                    started = time.monotonic()
                    rank, pivots, complete = rank_mod(matrix, prime, min(deadline, started + args.case_seconds))
                    record = dict(d=d, q=q, rows=len(matrix), columns=len(matrix[0]),
                                  prime=prime, beta=beta.tolist(), r=r.tolist(), rank=rank,
                                  elimination_complete=complete,
                                  full_row_rank=(rank == len(matrix)),
                                  elapsed_seconds=time.monotonic()-started,
                                  interpretation='auxiliary finite-field rank only; no head lower bound')
                    line = json.dumps(record)
                    log.write(line + '\n')
                    print(line, flush=True)


if __name__ == '__main__':
    main()
