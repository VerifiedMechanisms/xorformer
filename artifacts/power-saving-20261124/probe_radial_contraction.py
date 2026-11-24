#!/usr/bin/env python3
"""Probe label loss under a fixed-direction denominator contraction.

Numerical discovery only. Exact certificates are verified separately.
This tests a proposed reduction, not the main lower bound.
"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog


def features(x, slopes, t):
    den = 1 + t * (x @ slopes.T)
    return np.column_stack([np.ones(len(x))] +
                           [x / den[:, [h]] for h in range(len(slopes))])


def feasible(mat, labels):
    signed = labels[:, None] * mat
    result = linprog(np.zeros(mat.shape[1]), A_ub=-signed,
                     b_ub=-np.ones(len(labels)),
                     bounds=[(None, None)] * mat.shape[1], method="highs")
    if result.success:
        margin = float(np.min(signed @ result.x))
        if margin > 0.999:
            return True, result.x.tolist(), margin
        return None, None, margin
    if result.status == 2:
        dual = linprog(np.zeros(len(labels)),
                       A_eq=np.vstack([signed.T, np.ones(len(labels))]),
                       b_eq=np.r_[np.zeros(mat.shape[1]), 1],
                       bounds=[(0, None)] * len(labels), method="highs")
        if dual.success:
            return False, dual.x.tolist(), float(np.max(np.abs(signed.T @ dual.x)))
    return None, None, str(result.message)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=20261124)
    ap.add_argument("--n", type=int, default=4)
    ap.add_argument("--heads", type=int, default=2)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    start = time.monotonic()
    rng = np.random.default_rng(args.seed)
    x = ((np.arange(2 ** args.n)[:, None] >> np.arange(args.n)) & 1).astype(float)
    record = {"started_utc": datetime.now(timezone.utc).isoformat(),
              "n": args.n, "heads": args.heads, "seed": args.seed,
              "t_small": [1, 1000], "t_large": [1, 1], "results": []}
    for trial in range(args.trials):
        slopes = rng.integers(1, 10, size=(args.heads, args.n))
        small = features(x, slopes, 0.001)
        large = features(x, slopes, 1.0)
        # Draw both uniform labels and labels realized by a random large-scale
        # score. The second kind targets possible lost chambers efficiently.
        if trial % 2:
            labels = rng.choice([-1, 1], len(x))
        else:
            coefficients = rng.normal(size=large.shape[1])
            coefficients[0] = -np.median(large[:, 1:] @ coefficients[1:])
            labels = np.where(large @ coefficients > 0, 1, -1)
        ok_large, cert_large, residual_large = feasible(large, labels)
        if not ok_large:
            continue
        ok_small, cert_small, residual_small = feasible(small, labels)
        if ok_small is False:
            hit = {"trial": trial, "slopes": slopes.tolist(),
                   "labels": labels.tolist(), "large_coefficients": cert_large,
                   "small_dual": cert_small,
                   "large_margin": residual_large,
                   "small_dual_residual": residual_small}
            record["results"].append(hit)
            print(json.dumps({"trial": trial, "hit": len(record["results"]),
                              "elapsed_seconds": time.monotonic()-start}), flush=True)
            if len(record["results"]) >= 5:
                break
    record["elapsed_seconds"] = time.monotonic() - start
    record["finished_utc"] = datetime.now(timezone.utc).isoformat()
    args.out.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"hits": len(record["results"]),
                      "elapsed_seconds": record["elapsed_seconds"]}), flush=True)


if __name__ == "__main__":
    main()
