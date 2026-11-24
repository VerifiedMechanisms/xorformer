#!/usr/bin/env python3
"""Exact modular certificates for distinct-pole affine tangent matrices.

A nonzero modular maximal minor certifies real full row rank because every
entry is rational and every denominator is invertible modulo the prime.
This computation does not establish an asymptotic rank or orthant theorem.
Run with heavy for larger dimensions on shared machines.
"""
import argparse
import json
import numpy as np


def rank_certificate(matrix, prime):
    a = matrix.copy()
    rows, cols = a.shape
    rank = 0
    pivot_columns = []
    determinant = 1
    for col in range(cols):
        if rank == rows:
            break
        nonzero = np.flatnonzero(a[rank:, col])
        if not len(nonzero):
            continue
        pivot_row = rank + int(nonzero[0])
        if pivot_row != rank:
            a[[rank, pivot_row]] = a[[pivot_row, rank]]
            determinant = -determinant % prime
        pivot = int(a[rank, col])
        determinant = determinant * pivot % prime
        a[rank] = a[rank] * pow(pivot, -1, prime) % prime
        for row in range(rank + 1, rows):
            coefficient = int(a[row, col])
            if coefficient:
                a[row] = (a[row] - coefficient * a[rank]) % prime
        pivot_columns.append(col)
        rank += 1
    return {"rank": rank, "pivot_columns": pivot_columns,
            "maximal_minor_mod_prime": determinant if rank == rows else None}


def measure(k, prime):
    n = 1 << k
    h = (n + k) // (k + 1)
    scale = 100 * h
    words = np.arange(n, dtype=np.int64)
    bits = ((words[:, None] >> np.arange(k)) & 1).astype(np.int64)
    features = np.column_stack([np.ones(n, dtype=np.int64), bits])
    # b_j=1+(j+1)/(100H), w_i=2^i/(100H), so D=(100H+j+1+x)/(100H).
    denominator = scale + words[:, None] + np.arange(1, h + 1)[None, :]
    if np.any(denominator % prime == 0):
        raise ValueError("prime divides a denominator")
    reciprocal_square = np.array([
        [scale * scale * pow(int(value), -2, prime) % prime for value in row]
        for row in denominator], dtype=np.int64)
    matrix = (features[:, :, None] * reciprocal_square[:, None, :]).reshape(n, (k + 1) * h)
    result = {"dimension": k, "rows": n, "heads": h, "scale": scale,
              "prime": prime, **rank_certificate(matrix, prime)}
    print(json.dumps({key: result[key] for key in
                      ["dimension", "rows", "heads", "rank", "maximal_minor_mod_prime"]}), flush=True)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--dimension", type=int, nargs="+", default=list(range(2, 10)))
    parser.add_argument("--prime", type=int, default=65521)
    parser.add_argument("--output", default="/tmp/LargeDomainTangentRank.json")
    args = parser.parse_args()
    if args.prime ** 2 > np.iinfo(np.int64).max:
        raise ValueError("prime too large for exact int64 row operations")
    data = {"status": "finite exact computation; no orthant-cover conclusion",
            "formula": "F[x,(i,h)]=x_affine[i]/(1+(h+1+x)/(100H))^2",
            "results": [measure(k, args.prime) for k in args.dimension]}
    with open(args.output, "w") as target:
        json.dump(data, target, indent=2)
        target.write("\n")
