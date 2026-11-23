#!/usr/bin/env python3
"""Finite-field diagnostic for an affine permutation moment construction.

This computes the rank of the constant-in-s first variation at the
explicit (n+1)-root permutation cube. It is a finite diagnostic, not a
universal head bound and not a characteristic-zero rank certificate.
Run via heavy. Requires python-flint.
"""
import argparse
import json
import math
import time
from pathlib import Path
from flint import nmod_mat


def matrix(n, prime):
    m = n + 1
    variables = 2 * m * m
    d = [((-1) ** j * math.factorial(j) * math.factorial(n-j)) % prime
         for j in range(m)]
    constraints, outputs = [], []
    for mask in range(1 << n):
        x = [(mask >> i) & 1 for i in range(n)]
        z = [1] + x
        roots = [sum(x)] + [k * (1-x[k-1]) + sum(x[k:])
                            for k in range(1, m)]
        assert sorted(roots) == list(range(m))
        inv = [roots.index(j) for j in range(m)]
        vectors = []
        for j in range(m):
            row = [0] * variables
            for i, value in enumerate(z):
                row[inv[j] * m + i] = d[j] * value % prime
                row[m*m + j*m + i] = -d[j] * value % prime
            vectors.append(row)
        outputs.append(vectors[0])
        constraints.extend([[(a-b) % prime for a,b in zip(vectors[j], vectors[0])]
                            for j in range(1,m)])
    return constraints, outputs, variables


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--max-n", type=int, default=10)
    p.add_argument("--prime", type=int, default=2147483647)
    p.add_argument("--out", type=Path, required=True)
    a = p.parse_args()
    rows = []
    for n in range(1, a.max_n+1):
        start = time.monotonic()
        c, r, variables = matrix(n, a.prime)
        rank_c = nmod_mat(c, a.prime).rank()
        rank_cr = nmod_mat(c+r, a.prime).rank()
        event = dict(n=n, variables=variables, constraints=len(c),
                     constraint_rank=rank_c, combined_rank=rank_cr,
                     tangent_output_dimension=rank_cr-rank_c,
                     seconds=time.monotonic()-start)
        rows.append(event)
        print(json.dumps(event), flush=True)
        a.out.write_text(json.dumps(dict(prime=a.prime, rows=rows,
            scope="Finite-field rank diagnostic only; no characteristic-zero rank or universal construction claimed."), indent=2)+"\n")


if __name__ == "__main__":
    main()
