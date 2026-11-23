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
    p.add_argument("--second-order", action="store_true",
                   help="Also test specified first variations with a=0, b_j=-r/d_j.")
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
        if a.second_order and n >= 4:
            d = [((-1)**j * math.factorial(j) * math.factorial(n-j)) % a.prime
                 for j in range(n+1)]
            kappa = [sum(pow((ell-j) % a.prime,-1,a.prime)
                         for ell in range(n+1) if ell != j)
                     *pow(d[j],-1,a.prime) % a.prime for j in range(n+1)]
            probes=[]
            for coordinates in ([0],[0,1],[0,n-1],[n-2,n-1],list(range(n))):
                rhs=[]
                for mask in range(1 << n):
                    value=sum((mask >> i) & 1 for i in coordinates)
                    rhs.extend([(-(kappa[j]-kappa[0])*value*value) % a.prime
                                for j in range(1,n+1)])
                augmented=nmod_mat([row+[v] for row,v in zip(c,rhs)],a.prime)
                aug_rank=augmented.rank()
                probes.append(dict(zero_based_coordinates=coordinates,
                    augmented_rank=aug_rank,
                    consistent_over_finite_field=(aug_rank == rank_c)))
            event['specified_second_order_probes']=probes
        rows.append(event)
        print(json.dumps(event), flush=True)
        a.out.write_text(json.dumps(dict(prime=a.prime, rows=rows,
            scope="Finite-field rank diagnostic only; no characteristic-zero rank or universal construction claimed."), indent=2)+"\n")


if __name__ == "__main__":
    main()
