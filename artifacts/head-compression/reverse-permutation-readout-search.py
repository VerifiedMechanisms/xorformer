#!/usr/bin/env python3
"""Finite permutation readout probes, with exact rational witness checks.

This searches for q fixed queries whose signs on H! token permutations cover
all 2**q patterns. It proves no asymptotic compiler and uses no axis repair.
The compact Cauchy family uses positive denominators D+v_h-u_j. The free
assignment-cost family is a comparison class, not a head construction.
Run with heavy. All array computations use one thread.
"""
import os
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import time
import numpy as np


def exact_cost(query, h):
    if query["family"] == "free":
        return [[Fraction(v) for v in row] for row in query["cost"]]
    d = query["D"]
    a, v, mu = query["A"], query["v"], query["mu"]
    raw = [[Fraction(a[i] + mu[j], d + v[i] - j - 1)
            for j in range(h)] for i in range(h)]
    return [[(raw[i][j] - raw[i][0] - raw[0][j] + raw[0][0]) * d * d
             for j in range(h)] for i in range(h)]


def candidate(rng, h, family, d, mu):
    if family == "free":
        c = rng.integers(-100, 101, (h, h))
        return c.astype(float), {"family": family, "cost": c.tolist()}
    a = rng.integers(-100, 101, h)
    v = rng.integers(-10, 11, h)
    query = {"family": family, "D": d, "A": a.tolist(),
             "v": v.tolist(), "mu": mu.tolist()}
    ld = np.longdouble
    raw = (a[:, None].astype(ld) + mu[None, :].astype(ld)) / (
        ld(d) + v[:, None].astype(ld) - np.arange(1, h + 1, dtype=ld)[None, :])
    cost = (raw - raw[:, :1] - raw[:1, :] + raw[0, 0]) * d * d
    return np.asarray(cost, dtype=float), query


def run(h, family, seed, candidates, d, out):
    start = time.monotonic()
    rng = np.random.default_rng(seed)
    perms = np.array(list(itertools.permutations(range(h))), dtype=np.int16)
    labels = np.zeros(len(perms), dtype=np.int64)
    mu = rng.integers(-100, 101, h)
    queries = []
    diagnostics = []
    while 2 ** (len(queries) + 1) <= len(perms):
        order = np.argsort(labels, kind="stable")
        starts = np.flatnonzero(np.r_[True, np.diff(labels[order]) != 0])
        assert len(starts) == 2 ** len(queries)
        best = None
        best_gap = -float("inf")
        for _ in range(candidates):
            cost, query = candidate(rng, h, family, d, mu)
            score = cost[np.arange(h)[None, :], perms].sum(axis=1)
            arranged = score[order]
            lower = float(np.maximum.reduceat(arranged, starts).min())
            upper = float(np.minimum.reduceat(arranged, starts).max())
            gap = (lower - upper) / max(1.0, float(np.std(score)))
            if gap > best_gap:
                best_gap = gap
                best = (query, score, (lower + upper) / 2)
        diagnostics.append({"next_bit": len(queries) + 1,
                            "best_normalized_split_gap": best_gap})
        if best_gap <= 1e-10:
            break
        query, score, threshold = best
        cut = Fraction(float(threshold)).limit_denominator(10**10) + Fraction(1, 100000000003)
        query["threshold"] = [cut.numerator, cut.denominator]
        labels = labels * 2 + (score > float(cut))
        assert len(np.unique(labels)) == 2 ** (len(queries) + 1)
        queries.append(query)
        print(json.dumps({"family": family, "H": h, "seed": seed,
                          "bits": len(queries), "gap": best_gap}), flush=True)
    witness_ids = [int(np.flatnonzero(labels == k)[0])
                   for k in range(2 ** len(queries))]
    matrices = [exact_cost(q, h) for q in queries]
    min_margin = None
    for label, idx in enumerate(witness_ids):
        recovered = 0
        for q, cost in zip(queries, matrices):
            value = sum((cost[i][int(perms[idx, i])] for i in range(h)), Fraction(0))
            value -= Fraction(*q["threshold"])
            assert value != 0
            recovered = recovered * 2 + int(value > 0)
            margin = abs(value)
            min_margin = margin if min_margin is None else min(min_margin, margin)
        assert recovered == label
    result = {"H": h, "family": family, "seed": seed,
              "candidate_count_per_bit": candidates,
              "bits": len(queries), "permutations": len(perms),
              "queries": queries, "witnesses": [perms[i].tolist() for i in witness_ids],
              "diagnostics": diagnostics, "seconds": time.monotonic() - start,
              "exact_witness_check": True,
              "minimum_exact_margin": None if min_margin is None else
                  [min_margin.numerator, min_margin.denominator],
              "scope": "Finite permutation readouts only; no universal or axis-zero compiler.",
              "asymptotic_target_proved": False}
    path = out / f"{family}-h{h}-s{seed}.json"
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("H", "family", "seed", "bits", "seconds",
                                             "exact_witness_check")}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--heads", nargs="+", type=int, default=[5, 6, 7])
    parser.add_argument("--seeds", nargs="+", type=int, default=[11, 29])
    parser.add_argument("--candidates", type=int, default=256)
    parser.add_argument("--D", type=int, default=1000)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    for h in args.heads:
        for seed in args.seeds:
            for family in ("compact_cauchy", "free"):
                run(h, family, seed, args.candidates, args.D, args.out)


if __name__ == "__main__":
    main()
