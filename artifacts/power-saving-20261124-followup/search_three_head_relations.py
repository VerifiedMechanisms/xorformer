#!/usr/bin/env python3
"""Exact finite-field search for genuinely three-head Boolean dependencies.

Run as `heavy python3 ... --dimension 6 --alphabet 3 --output PATH`.
A full column rank modulo PRIME certifies full rank over the rationals.
A deficient modular rank is only a candidate and needs an exact rational audit.
Coordinate permutations and head permutations are removed exactly. This is a
finite search over denominators 1 + sum_i b_i*x_i with b_i in [1,alphabet].
It proves no statement about unrestricted real denominator configurations.
"""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import permutations, product
import json
from pathlib import Path
import time
import numpy as np

PRIME = 1000003


def rankmod(matrix):
    matrix = matrix.copy()
    rows, columns = matrix.shape
    rank = 0
    for column in range(columns):
        nonzero = np.flatnonzero(matrix[rank:, column])
        if not len(nonzero):
            continue
        pivot = rank + int(nonzero[0])
        matrix[[rank, pivot]] = matrix[[pivot, rank]]
        matrix[rank, column:] = (
            matrix[rank, column:] * pow(int(matrix[rank, column]), -1, PRIME)
        ) % PRIME
        matrix[rank + 1:, column:] = (
            matrix[rank + 1:, column:]
            - matrix[rank + 1:, column, None] * matrix[rank, None, column:]
        ) % PRIME
        rank += 1
        if rank == rows:
            break
    return rank


def compositions(total, length):
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for rest in compositions(total - first, length - 1):
                yield (first,) + rest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dimension', type=int, required=True)
    parser.add_argument('--alphabet', type=int, default=3)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--stop-at-candidate', action='store_true')
    args = parser.parse_args()
    n, alphabet = args.dimension, args.alphabet
    cube = np.array(list(product([0, 1], repeat=n)), dtype=np.int64)
    one = np.ones((len(cube), 1), dtype=np.int64)
    inverse = np.array([0] + [pow(i, -1, PRIME) for i in range(1, alphabet*n+2)],
                       dtype=np.int64)
    types = list(product(range(1, alphabet+1), repeat=3))
    lookup = {item: i for i, item in enumerate(types)}
    maps = [tuple(lookup[tuple(item[j] for j in perm)] for item in types)
            for perm in permutations(range(3))]
    started = time.monotonic()
    counts_seen = canonical_seen = full_pair_seen = 0
    rank_counts = Counter()
    candidates = []

    @lru_cache(maxsize=200000)
    def pair_full(pair_columns):
        b = np.array(pair_columns, dtype=np.int64).T
        features = [cube * inverse[1 + cube @ row, None] % PRIME for row in b]
        return rankmod(np.concatenate([one] + features, axis=1)) == 1 + 2*n

    def save(complete):
        result = dict(dimension=n, alphabet=alphabet, prime=PRIME,
                      denominator_constant=1, complete=complete,
                      coordinate_multisets=counts_seen,
                      canonical_distinct_head_configurations=canonical_seen,
                      full_pair_configurations=full_pair_seen,
                      triple_rank_histogram=dict(rank_counts), candidates=candidates,
                      pair_cache=str(pair_full.cache_info()),
                      elapsed_seconds=time.monotonic()-started)
        temporary = args.output.with_suffix('.tmp')
        temporary.write_text(json.dumps(result, indent=2) + '\n')
        temporary.replace(args.output)
        print(json.dumps({key: value for key, value in result.items()
                          if key != 'candidates'}), flush=True)

    next_report = started + 45
    for counts in compositions(n, len(types)):
        counts_seen += 1
        canonical = True
        for mapping in maps[1:]:
            transformed = [0] * len(types)
            for i, multiplicity in enumerate(counts):
                transformed[mapping[i]] = multiplicity
            if tuple(transformed) < counts:
                canonical = False
                break
        if not canonical:
            continue
        columns = [item for item, multiplicity in zip(types, counts)
                   for _ in range(multiplicity)]
        b = np.array(columns, dtype=np.int64).T
        if any(np.array_equal(b[i], b[j]) for i, j in [(0,1), (0,2), (1,2)]):
            continue
        canonical_seen += 1
        full_pairs = True
        for i, j in [(0,1), (0,2), (1,2)]:
            key1 = tuple(sorted((int(a), int(c)) for a, c in zip(b[i], b[j])))
            key2 = tuple(sorted((c, a) for a, c in key1))
            if not pair_full(min(key1, key2)):
                full_pairs = False
                break
        if full_pairs:
            full_pair_seen += 1
            features = [cube * inverse[1 + cube @ row, None] % PRIME for row in b]
            rank = rankmod(np.concatenate([one] + features, axis=1))
            rank_counts[rank] += 1
            if rank < 1 + 3*n:
                candidates.append(dict(slopes=b.tolist(), modular_rank=rank))
                if args.stop_at_candidate:
                    save(False)
                    return
        if time.monotonic() >= next_report:
            save(False)
            next_report = time.monotonic() + 45
    save(True)


if __name__ == '__main__':
    main()
