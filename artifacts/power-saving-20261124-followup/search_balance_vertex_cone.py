#!/usr/bin/env python3
"""Floating search for a unit-feasible basis cone missing all coordinate rays.

Every candidate is checked on the full cube. This is exploratory evidence only;
an output needs an independent rational reconstruction. Run with ``heavy``.
"""
import argparse
import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

parser = argparse.ArgumentParser()
parser.add_argument("--n", type=int, default=8)
parser.add_argument("--seconds", type=int, default=180)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--power", action="store_true")
parser.add_argument("--objective-range", type=float, default=8)
parser.add_argument("--nonunimodular", action="store_true")
parser.add_argument("--balance-only", action="store_true")
parser.add_argument("--weight-range", type=float, default=5)
parser.add_argument("--pole-range", type=float, default=12)
args = parser.parse_args()
n = args.n
d = n + 1
count = 2**n
rng = np.random.default_rng(425378)
rows = np.array([[1] + [(x >> (n - 1 - i)) & 1 for i in range(n)]
                 for x in range(count)], dtype=float)
start = time.monotonic()
trials = 0
feasible = 0
records = []
best = 1.0
while time.monotonic() - start < args.seconds:
    trials += 1
    weights = rng.normal(size=d) * np.exp(rng.uniform(0, args.weight_range, size=d))
    weights[0] = -weights[1:].sum() / 2 + rng.normal() * np.linalg.norm(weights[1:]) * .3
    labels = np.where(rows @ weights > 0, 1., -1.)
    signed = labels[:, None] * rows
    pole = np.exp(rng.uniform(-args.pole_range, 0, size=d))
    if trials % 2:
        pole[0] = 10**rng.uniform(-10, -3)
    pole /= pole.sum()
    objective = signed.T @ np.exp(rng.uniform(-args.objective_range, 0, size=count))
    fit = linprog(objective, A_ub=-signed, b_ub=-(rows @ pole),
                  bounds=[(None, None)] * d, method="highs")
    if not fit.success:
        continue
    residual = signed @ fit.x - rows @ pole
    if residual.min() < -1e-7:
        continue
    basis = []
    for index in np.flatnonzero(np.abs(residual) < 1e-7):
        if np.linalg.matrix_rank(rows[basis + [index]]) > len(basis):
            basis.append(int(index))
        if len(basis) == d:
            break
    if len(basis) != d:
        continue
    transform = np.linalg.solve(rows[basis], labels[basis, None] * rows[basis])
    constraints = labels[:, None] * (rows @ transform) - rows
    if (constraints @ pole).min() < -1e-6:
        continue
    feasible += 1
    rays = np.flatnonzero(constraints.min(axis=0) >= -1e-7).tolist()
    determinant = int(round(np.linalg.det(rows[basis])))
    if args.nonunimodular and abs(determinant) > 1:
        record = {"trial": trials, "elapsed": time.monotonic() - start,
                  "basis": basis, "basis_labels": labels[basis].tolist(),
                  "full_labels": labels.tolist(), "matrix": transform.tolist(),
                  "original_b": pole.tolist(), "feasible_rays": rays,
                  "determinant": determinant}
        records.append(record)
        print({key: record[key] for key in ("trial", "elapsed", "feasible_rays", "determinant")}, flush=True)
        break
    power_gap = float((constraints @ (pole * pole)).min())
    if args.power and power_gap < -1e-6:
        record = {"trial": trials, "elapsed": time.monotonic() - start,
                  "basis": basis, "basis_labels": labels[basis].tolist(),
                  "full_labels": labels.tolist(), "matrix": transform.tolist(),
                  "original_b": pole.tolist(), "feasible_rays": rays,
                  "squared_coefficient_gap": power_gap}
        records.append(record)
        print({key: record[key] for key in ("trial", "elapsed", "feasible_rays", "squared_coefficient_gap")}, flush=True)
        break
    if rays and trials % 20 and not args.balance_only:
        continue
    balance = linprog(np.r_[-1., np.zeros(n)], A_ub=-constraints,
                      b_ub=np.zeros(count), A_eq=np.ones((1, d)), b_eq=[1.],
                      bounds=[(0, None)] * d, method="highs")
    if not balance.success:
        continue
    value = float(balance.x[0])
    if (rays or args.balance_only) and value >= best - 1e-7:
        continue
    best = min(best, value)
    record = {"trial": trials, "elapsed": time.monotonic() - start,
              "basis": basis, "basis_labels": labels[basis].tolist(),
              "full_labels": labels.tolist(), "matrix": transform.tolist(),
              "original_b": pole.tolist(), "max_b0": value,
              "balanced_b": balance.x.tolist(), "feasible_rays": rays}
    records.append(record)
    print({key: record[key] for key in ("trial", "elapsed", "max_b0", "feasible_rays")}, flush=True)
    if not rays and not args.balance_only:
        break
args.output.write_text(json.dumps({"warning": "Floating exploratory evidence only",
                                  "n": n, "trials": trials, "feasible": feasible,
                                  "records": records}, indent=2) + "\n")
print({"trials": trials, "feasible": feasible, "best": best}, flush=True)
