#!/usr/bin/env python3
"""Exact finite-field ranks of Boolean block Krylov spaces.

A nonzero modular minor certifies real independence for the integer matrix.
These finite computations assert no asymptotic rank formula or sign coverage.
"""
import argparse
import json
import numpy as np


def ranks(k, prime):
    size = 1 << k
    points = np.arange(size, dtype=np.int64)
    features = [np.ones(size, dtype=np.int64)]
    features += [((points >> i) & 1) for i in range(k)]
    basis = []
    pivots = []
    power = np.ones(size, dtype=np.int64)
    history = []
    for degree in range(size):
        old_rank = len(basis)
        for feature in features:
            col = feature * power % prime
            for pivot, vec in zip(pivots, basis):
                if col[pivot]:
                    col = (col - col[pivot] * vec) % prime
            nonzero = np.flatnonzero(col)
            if len(nonzero):
                pivot = int(nonzero[0])
                col = col * pow(int(col[pivot]), -1, prime) % prime
                pivots.append(pivot)
                basis.append(col)
        history.append({'degree': degree, 'rank': len(basis),
                        'increment': len(basis)-old_rank})
        if len(basis) == size:
            break
        power = power * points % prime
    return {'k': k, 'size': size, 'prime': prime, 'history': history}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-k', type=int, default=10)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    result = []
    for k in range(1, args.max_k + 1):
        row = ranks(k, 65521)
        result.append(row)
        print(k, row['history'][-1], flush=True)
    with open(args.output, 'w') as out:
        json.dump({'status': 'finite exact modular computation',
                   'ranks': result}, out, indent=2)
        out.write('\n')

if __name__ == '__main__':
    main()
