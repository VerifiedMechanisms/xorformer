#!/usr/bin/env python3
"""Exact pair-span matching for signed powers of two.

Coordinates are stored as signs and integer exponents, so extremely separated
scales require no large integer allocation. A witness has coefficients
alpha in {-1,1} and beta = beta_sign * 2**(beta_twice_exponent/2).
Every selected edge is checked by integer comparisons of exponents. This is
only a finite dictionary experiment and does not prove a universal head bound.
The correlated model enumerates all sign words and sets their exponent vectors
by a shared integer matrix. The independent-distribution obstruction does not
apply to this correlated model.
Run through heavy.
"""
import argparse
import json
import os
from pathlib import Path
import time

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import maximum_bipartite_matching

INF = 1 << 60


def witness(vsign, vexp, wsign, wexp, sigma):
    for alpha in (1, -1):
        for beta_sign in (1, -1):
            u = alpha * vsign * sigma
            w = beta_sign * wsign * sigma
            if np.any((u < 0) & (w < 0)):
                continue
            delta = vexp - wexp
            lower = delta[(u < 0) & (w > 0)]
            upper = delta[(u > 0) & (w < 0)]
            lo = int(np.max(lower)) if len(lower) else -INF
            hi = int(np.min(upper)) if len(upper) else INF
            if lo >= hi:
                continue
            twice = lo + hi if lo > -INF and hi < INF else (
                2 * lo + 1 if lo > -INF else 2 * hi - 1 if hi < INF else 0)
            for a, ea, b, eb in zip(u, vexp, w, wexp):
                assert (a > 0 and b > 0) or (
                    a > 0 and 2 * int(ea) > 2 * int(eb) + twice) or (
                    b > 0 and 2 * int(eb) + twice > 2 * int(ea))
            return [alpha, beta_sign, twice]
    return None


def check(k, seed, samples, out, deadline, side_factor, model="independent"):
    rng = np.random.default_rng(seed)
    side = side_factor * (1 << k)
    matrices = np.empty((0, k, k), dtype=np.int64)
    if model == "independent":
        signs = rng.choice(np.array([-1, 1], dtype=np.int8), size=(2 * side, k))
        exponents = rng.integers(0, 1 << 30, size=(2 * side, k), dtype=np.int64)
    else:
        words = (1 - 2 * ((np.arange(1 << k)[:, None] >> np.arange(k)) & 1))
        words = words.astype(np.int8)
        matrices = rng.integers(-(1 << 20), 1 << 20,
                                size=(2 * side_factor, k, k), dtype=np.int64)
        if model == "correlated-skew":
            matrices = matrices - matrices.transpose(0, 2, 1)
        elif model == "correlated-symmetric":
            matrices = matrices + matrices.transpose(0, 2, 1)
        signs = np.concatenate([words[rng.permutation(1 << k)]
                                for _ in matrices])
        exponents = np.concatenate([
            signs[j * (1 << k):(j + 1) * (1 << k)].astype(np.int64) @ matrix.T
            for j, matrix in enumerate(matrices)])
    np.savez(out / "dictionary.npz", signs=signs, exponents=exponents,
             matrices=matrices)
    masks = np.arange(1 << k) if samples >= 1 << k else rng.choice(
        1 << k, samples, replace=False)
    for mask in masks:
        if time.monotonic() >= deadline:
            break
        sigma = 1 - 2 * ((int(mask) >> np.arange(k)) & 1)
        rows, cols = [], []
        for start in range(0, side, 16):
            delta = exponents[start:start+16, None, :] - exponents[None, side:, :]
            allowed = np.zeros(delta.shape[:2], dtype=bool)
            for alpha in (1, -1):
                u = alpha * signs[start:start+16, None, :] * sigma
                for beta_sign in (1, -1):
                    w = beta_sign * signs[None, side:, :] * sigma
                    compatible = ~np.any((u < 0) & (w < 0), axis=2)
                    lo = np.max(np.where((u < 0) & (w > 0), delta, -INF), axis=2)
                    hi = np.min(np.where((u > 0) & (w < 0), delta, INF), axis=2)
                    allowed |= compatible & (lo < hi)
            rr, cc = np.nonzero(allowed)
            rows.extend((rr + start).tolist())
            cols.extend(cc.tolist())
        graph = csr_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)),
                           shape=(side, side))
        matching = maximum_bipartite_matching(graph, perm_type="column")
        certificate = []
        for i, j in enumerate(matching):
            if j >= 0:
                j = int(j) + side
                coefficients = witness(signs[i], exponents[i], signs[j], exponents[j], sigma)
                assert coefficients is not None
                certificate.append([i, j, *coefficients])
        record = {"k": k, "seed": seed, "orthant_mask": int(mask),
                  "dictionary_size": 2 * side, "matching_size": len(certificate),
                  "fraction_of_dictionary": len(certificate) / (2 * side),
                  "isolated_left": int(np.count_nonzero(graph.getnnz(axis=1) == 0)),
                  "isolated_right": int(np.count_nonzero(graph.getnnz(axis=0) == 0)),
                  "edges": len(rows), "exact_edge_checks": True,
                  "coordinate_model": model,
                  "scope": "This finite dictionary and orthant only."}
        (out / f"orthant-{int(mask)}.json").write_text(
            json.dumps({**record, "matching": certificate}) + "\n")
        print(json.dumps(record), flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=3000)
    p.add_argument("--samples", type=int, default=16)
    p.add_argument("--side-factor", type=int, default=4)
    p.add_argument("--dimensions", type=int, nargs="+", default=[6, 8, 10, 11])
    p.add_argument("--model", choices=["independent", "correlated-linear",
                   "correlated-skew", "correlated-symmetric"], default="independent")
    p.add_argument("--max-trials", type=int, default=0,
                   help="Stop after this many dictionaries; zero means deadline only.")
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + args.seconds
    trial = 0
    while time.monotonic() < deadline and (not args.max_trials or trial < args.max_trials):
        k = args.dimensions[trial % len(args.dimensions)]
        seed = 370000 + trial
        out = args.out / f"k{k}-seed{seed}"
        out.mkdir(exist_ok=True)
        check(k, seed, args.samples, out, deadline, args.side_factor, args.model)
        trial += 1


if __name__ == "__main__":
    main()
