#!/usr/bin/env python3
"""Exact finite-field ranks of moment-curve jet spaces, not real-rank proofs.

The row inputs are the nonzero k-bit words. At order a, include evaluations
P_x(t)^a for t=1,...,ka+1, which span the coefficient functions of P_x(T)^a
over this field when ka+1<p. Report the rank and coordinates forced to zero
in the annihilator. Finite-field conclusions are not silently transferred
to real rank or to permutation orthant coverage.
"""

import argparse
import json
import numpy as np


def measure(k, max_degree, prime):
    words = np.arange(1, 1 << k, dtype=np.int64)
    bits = ((words[:, None] >> np.arange(k)) & 1).astype(np.int64)
    basis = []
    pivots = []
    reports = []
    for a in range(1, max_degree + 1):
        if k * a + 1 >= prime:
            raise ValueError("prime too small for coefficient/evaluation equivalence")
        for t in range(1, k * a + 2):
            powers = np.array([pow(t, i + 1, prime) for i in range(k)], dtype=np.int64)
            vals = (bits @ powers) % prime
            vec = np.array([pow(int(v), a, prime) for v in vals], dtype=np.int64)
            for row, pivot in zip(basis, pivots):
                coefficient = int(vec[pivot])
                if coefficient:
                    vec = (vec - coefficient * row) % prime
            support = np.flatnonzero(vec)
            if not len(support):
                continue
            pivot = int(support[0])
            vec = (vec * pow(int(vec[pivot]), -1, prime)) % prime
            basis.append(vec)
            pivots.append(pivot)
        # Reduce the independent echelon rows backwards. A pivot coordinate
        # is zero in every annihilator iff its row has no nonpivot entry.
        reduced = np.array(basis, dtype=np.int64)
        for j in range(len(basis) - 1, -1, -1):
            for i in range(j):
                coefficient = int(reduced[i, pivots[j]])
                if coefficient:
                    reduced[i] = (reduced[i] - coefficient * reduced[j]) % prime
        free = sorted(set(range(len(words))) - set(pivots))
        forced = [int(words[pivots[i]]) for i in range(len(pivots))
                  if not free or not np.any(reduced[i, free])]
        report = {"degree": a, "rank": len(basis), "inputs": len(words),
                  "annihilator_forced_zero_words": forced}
        reports.append(report)
        print(json.dumps({"k": k, "prime": prime, "degree": a,
                          "rank": len(basis), "inputs": len(words),
                          "forced_zero_count": len(forced)}), flush=True)
        if len(basis) == len(words):
            break
    return {"k": k, "prime": prime, "reports": reports}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", nargs="+", type=int, default=[4, 5, 6, 7, 8])
    parser.add_argument("--max-degree", type=int, default=24)
    parser.add_argument("--prime", type=int, default=65521)
    parser.add_argument("--output", default="/tmp/JointFamilyMomentJetRanks.json")
    args = parser.parse_args()
    result = [measure(k, args.max_degree, args.prime) for k in args.k]
    with open(args.output, "w") as output:
        json.dump({"status": "finite-field computation only", "results": result}, output, indent=2)
