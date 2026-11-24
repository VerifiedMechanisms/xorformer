#!/usr/bin/env python3
"""Exploratory floating MILP enumeration, not an exact cardinality certificate.

Use `heavy python3 ...`. A solver exhaustion result is only numerical evidence.
The fixed integer basis map is the Lean-checked seven-variable example.
"""
import argparse
import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=300)
    parser.add_argument("--epsilon", type=float, default=1e-3)
    parser.add_argument("--limit", type=int, default=1000)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    T = np.array([
        [-7, -6, -6, -6, -2, -6, -4, -4],
        [16, 13, 12, 12, 6, 10, 10, 8],
        [-12, -10, -9, -8, -4, -6, -8, -6],
        [18, 14, 14, 13, 6, 10, 12, 8],
        [-8, -6, -6, -6, -3, -4, -6, -4],
        [-6, -4, -4, -4, -2, -3, -4, -2],
        [2, 2, 2, 2, 0, 2, 1, 2],
        [-10, -8, -8, -8, -4, -6, -6, -5],
    ], dtype=float)
    n, d, N = 7, 8, 128
    X = np.array([[1] + [(j >> (n - 1 - i)) & 1 for i in range(n)]
                  for j in range(N)], dtype=float)
    U = X @ T
    big_m = 2 * np.max(np.abs(U)) + 2
    rows, lo, hi = [], [], []
    row = np.zeros(d + N)
    row[:d] = 1
    rows.append(row)
    lo.append(1)
    hi.append(1)
    for x in range(N):
        row = np.zeros(d + N)
        row[:d] = U[x] - X[x]
        row[d + x] = -big_m
        rows.append(row)
        lo.append(-big_m)
        hi.append(np.inf)
        row = np.zeros(d + N)
        row[:d] = -U[x] - X[x]
        row[d + x] = big_m
        rows.append(row)
        lo.append(0)
        hi.append(np.inf)
    bounds = Bounds(np.r_[np.full(d, args.epsilon), np.zeros(N)],
                    np.ones(d + N))
    integrality = np.r_[np.zeros(d), np.ones(N)]
    start = time.monotonic()
    records = []
    seen = set()
    status = "limit"
    while len(records) < args.limit:
        remaining = args.seconds - (time.monotonic() - start)
        if remaining <= 0:
            status = "wall_time"
            break
        result = milp(np.zeros(d + N), integrality=integrality,
                      bounds=bounds,
                      constraints=LinearConstraint(np.array(rows), lo, hi),
                      options={"time_limit": remaining, "mip_rel_gap": 0})
        if result.x is None:
            status = f"solver_{result.status}: {result.message}"
            break
        b = result.x[:d]
        a = T @ b
        bits = (U @ b > 0).astype(int)
        residual = np.abs(U @ b) - X @ b
        solver_bits = np.rint(result.x[d:]).astype(int)
        if not np.array_equal(bits, solver_bits):
            status = "numerical_failure: integer labels disagree with score signs"
            break
        if residual.min() < -1e-7:
            status = "numerical_failure: gap constraint violated"
            break
        key = tuple(bits)
        if key in seen:
            status = "numerical_failure: excluded pattern returned"
            break
        seen.add(key)
        records.append({"b": b.tolist(), "a": a.tolist(),
                        "positive_vertices": np.flatnonzero(bits).tolist(),
                        "min_residual": float(residual.min()),
                        "elapsed_seconds": time.monotonic() - start})
        row = np.zeros(d + N)
        row[d:] = 2 * bits - 1
        rows.append(row)
        lo.append(-np.inf)
        hi.append(int(bits.sum()) - 1)
        args.output.write_text(json.dumps({
            "warning": "Floating exploration only, not an exact proof",
            "epsilon": args.epsilon, "status": "running",
            "records": records,
        }, indent=2) + "\n")
    output = {"warning": "Floating exploration only, not an exact proof",
              "epsilon": args.epsilon, "status": status,
              "elapsed_seconds": time.monotonic() - start,
              "records": records}
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({k: v for k, v in output.items() if k != "records"}
                     | {"patterns_found": len(records)}))


if __name__ == "__main__":
    main()
