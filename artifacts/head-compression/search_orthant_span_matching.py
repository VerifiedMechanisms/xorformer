#!/usr/bin/env python3
"""Bipartite matching probe for two-vector spans meeting strict orthants.

This changes the fixed-difference routing mechanism by allowing free scalar
amplitudes. All selected edges are checked using exact rational inequalities.
Finite sampled orthants do not constitute an asymptotic construction. Use heavy.
"""
import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import time

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_bipartite_matching


def exact_amplitudes(v, w, sigma):
    v = [int(a)*int(s) for a, s in zip(v, sigma)]
    w = [int(a)*int(s) for a, s in zip(w, sigma)]
    for a in (1, -1):
        lower = [Fraction(-a*x, y) for x, y in zip(v, w) if y > 0]
        upper = [Fraction(-a*x, y) for x, y in zip(v, w) if y < 0]
        if any(a*x <= 0 for x, y in zip(v, w) if y == 0):
            continue
        lo = max(lower) if lower else None
        hi = min(upper) if upper else None
        if lo is not None and hi is not None and lo >= hi:
            continue
        b = (lo+hi)/2 if lo is not None and hi is not None else (
            lo+1 if lo is not None else hi-1 if hi is not None else Fraction(0))
        assert all(a*x+b*y > 0 for x, y in zip(v, w))
        return a, b
    return None


def check(k, seed, samples, out, deadline):
    rng = np.random.default_rng(seed)
    side = 4*(1 << k)
    points = np.rint(rng.normal(size=(2*side, k))*1000000).astype(np.int64)
    points[points == 0] = 1
    left, right = points[:side], points[side:]
    np.save(out / "dictionary.npy", points)
    masks = np.arange(1 << k) if samples >= 1 << k else rng.choice(1 << k, samples, replace=False)
    results = []
    for mask in masks:
        if time.monotonic() >= deadline:
            break
        sigma = 1-2*((int(mask) >> np.arange(k)) & 1)
        positive = right*sigma > 0
        rows, cols = [], []
        for start in range(0, side, 16):
            ratios = -left[start:start+16, None, :] / right[None, :, :]
            lo = np.max(np.where(positive[None], ratios, -np.inf), axis=2)
            hi = np.min(np.where(~positive[None], ratios, np.inf), axis=2)
            lo2 = np.max(np.where(positive[None], -ratios, -np.inf), axis=2)
            hi2 = np.min(np.where(~positive[None], -ratios, np.inf), axis=2)
            rr, cc = np.nonzero((lo < hi-1e-12) | (lo2 < hi2-1e-12))
            rows.extend((rr+start).tolist()); cols.extend(cc.tolist())
        graph = csr_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)), shape=(side, side))
        matching = maximum_bipartite_matching(graph, perm_type="column")
        certificate = []
        for i, j in enumerate(matching):
            if j >= 0:
                amplitude = exact_amplitudes(left[i], right[j], sigma)
                assert amplitude is not None
                a, b = amplitude
                certificate.append([i, int(j)+side, a, b.numerator, b.denominator])
        record = {"k": k, "seed": seed, "orthant_mask": int(mask),
                  "dictionary_size": 2*side, "matching_size": len(certificate),
                  "fraction_of_dictionary": len(certificate)/(2*side),
                  "isolated_left": int(np.count_nonzero(graph.getnnz(axis=1) == 0)),
                  "isolated_right": int(np.count_nonzero(graph.getnnz(axis=0) == 0)),
                  "edges": len(rows), "exact_edge_checks": True,
                  "scope": "This dictionary and orthant only; no universal theorem."}
        (out / f"orthant-{int(mask)}.json").write_text(json.dumps({**record, "matching": certificate})+"\n")
        results.append(record)
        print(json.dumps(record), flush=True)
    return results


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=6000)
    p.add_argument("--samples", type=int, default=32)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic()+args.seconds
    trial = 0
    while time.monotonic() < deadline:
        k = (5, 6, 7, 8, 9, 10)[trial % 6]
        seed = 350000+trial
        out = args.out / f"k{k}-seed{seed}"
        out.mkdir(exist_ok=True)
        check(k, seed, args.samples, out, deadline)
        trial += 1


if __name__ == "__main__":
    main()
