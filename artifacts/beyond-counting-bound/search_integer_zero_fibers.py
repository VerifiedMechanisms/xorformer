"""Search integer affine forms for coordinate zero-score rank certificates.

This is an exploratory search, not an asymptotic lower-bound computation.
All zero tests and retained ranks are exact. Failure to find a certificate is
reported only as UNKNOWN.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np


PRIME = 65521


def subset_sums(weights):
    heads, n = weights.shape
    sums = np.empty((1 << n, heads), dtype=np.int64)
    sums[0] = 0
    for i in range(n):
        count = 1 << i
        sums[count:2 * count] = sums[:count] + weights[:, i]
    return sums


def rank_and_pivots(matrix):
    a = matrix.copy() % PRIME
    row_ids = np.arange(len(a))
    chosen_rows, chosen_columns = [], []
    rank = 0
    for col in range(a.shape[1]):
        candidates = np.flatnonzero(a[rank:, col])
        if not len(candidates):
            continue
        pivot = rank + int(candidates[0])
        a[[rank, pivot]] = a[[pivot, rank]]
        row_ids[[rank, pivot]] = row_ids[[pivot, rank]]
        chosen_rows.append(int(row_ids[rank]))
        chosen_columns.append(col)
        a[rank] = a[rank] * pow(int(a[rank, col]), -1, PRIME) % PRIME
        a[rank + 1:] = (a[rank + 1:]
                       - a[rank + 1:, col, None] * a[rank]) % PRIME
        rank += 1
        if rank == min(a.shape):
            break
    return rank, chosen_rows, chosen_columns


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=14400)
    parser.add_argument('--seed', type=int, default=191347)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    start = time.monotonic()
    cases = [(12, 2), (14, 2), (16, 2), (16, 3), (18, 3), (20, 3)]
    best = {case: 0 for case in cases}
    targets = {(n, h): 2 * n * h - (3 if h == 2 else 0) for n, h in cases}
    trial = 0
    with (args.output / 'results.jsonl').open('a', buffering=1) as log:
        while time.monotonic() - start < args.seconds:
            n, heads = cases[trial % len(cases)]
            b = rng.integers(1, 5, size=(heads, n), dtype=np.int64)
            # Numerators are u = U / heads, centered near cancellation of bias.
            U = -b + rng.integers(-3, 4, size=(heads, n), dtype=np.int64)
            d = 1 + subset_sums(b)
            a = subset_sums(U)
            product = np.prod(d, axis=1)
            numerator = heads * product + np.sum(a * (product[:, None] // d), axis=1)
            zeros = np.flatnonzero(numerator == 0)
            record = dict(trial=trial, n=n, heads=heads, zeros=len(zeros),
                          elapsed_seconds=time.monotonic() - start, status='UNKNOWN')
            if len(zeros) > best[n, heads]:
                # Retain enough rows to determine a full column rank, if present.
                sample = zeros if len(zeros) <= 8 * n * heads else rng.choice(
                    zeros, 8 * n * heads, replace=False)
                x = ((sample[:, None] >> np.arange(n)) & 1).astype(np.int64)
                den = d[sample]
                inv = np.array([[pow(int(v), -1, PRIME) for v in row]
                                for row in den], dtype=np.int64)
                av = a[sample] * pow(heads, -1, PRIME) % PRIME
                ju = (x[:, None, :] * inv[:, :, None]).reshape(len(x), -1)
                scalar = (av * inv % PRIME) * inv % PRIME
                jb = (-x[:, None, :] * scalar[:, :, None]).reshape(len(x), -1)
                jacobian = np.concatenate([ju, jb], axis=1) % PRIME
                rank, rows, columns = rank_and_pivots(jacobian)
                record['certified_rank'] = rank
                if rank > best[n, heads]:
                    best[n, heads] = rank
                    cert = dict(record, denominator_slopes=b.tolist(),
                                numerator_scaled_slopes=U.tolist(),
                                numerator_scale=heads, prime=PRIME,
                                sample_indices=[int(sample[j]) for j in rows],
                                parameter_columns=columns)
                    filename = f'n{n}-h{heads}-rank{rank}-trial{trial}.json'
                    (args.output / filename).write_text(json.dumps(cert, indent=2) + '\n')
                    record.update(status='EXACT_RANK_CERTIFICATE', certificate=filename)
            if 'certified_rank' in record or trial % 30 == 0:
                log.write(json.dumps(record) + '\n')
                print(json.dumps(record), flush=True)
            trial += 1
            if all(best[case] >= targets[case] for case in cases):
                break
    print(json.dumps({'status': 'SEARCH_FINISHED', 'best_ranks': {
        f'n{n}-h{h}': r for (n, h), r in best.items()}, 'trials': trial}), flush=True)


if __name__ == '__main__':
    main()
