#!/usr/bin/env python3
"""Explore all feasible mixed-row branches of a supplied fixed Boolean basis.

Floating LP results are exploratory only. The matrix is reconstructed exactly
from the integer Boolean basis and signs before conversion to scipy.
Run under `heavy`.
"""
import argparse
import json
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.optimize import linprog

p = argparse.ArgumentParser()
p.add_argument("input", type=Path)
p.add_argument("output", type=Path)
args = p.parse_args()
data = json.loads(args.input.read_text())
n = data["n"]
d = n + 1
record = data["records"][-1] if "records" in data else data
Xexact = sp.Matrix([[1] + [(x >> (n - 1 - i)) & 1 for i in range(n)]
                   for x in range(2**n)])
Z = Xexact[record["basis"], :]
g = [int(t) for t in record["labels"]]
T = Z.inv() * sp.diag(*g) * Z
Uexact = Xexact * T
X = np.array(Xexact, dtype=float)
U = np.array(Uexact, dtype=float)
mixed = [i for i in range(2**n)
         if min(Uexact.row(i)) < 0 < max(Uexact.row(i))]
fixed = [i for i in range(2**n) if i not in mixed]
fixed_sign = np.sign(U[fixed].sum(axis=1))
base = fixed_sign[:, None] * U[fixed] - X[fixed]
branches = []
calls = 0

def solve(rows, objective=None, support=None):
    global calls
    calls += 1
    if objective is None:
        objective = np.zeros(d)
    bounds = [(0, None)] * d if support is None else [
        (0, None) if i in support else (0, 0) for i in range(d)]
    return linprog(objective, A_ub=-np.array(rows), b_ub=np.zeros(len(rows)),
                   A_eq=np.ones((1, d)), b_eq=[1], bounds=bounds,
                   method="highs")

def dfs(depth, rows, signs):
    if depth == len(mixed):
        # A strictly positive denominator coefficient vector is necessary.
        aug = np.c_[np.array(rows), np.zeros(len(rows))]
        aug = np.r_[aug, np.c_[np.eye(d), -np.ones(d)]]
        res = linprog(np.r_[np.zeros(d), -1.], A_ub=-aug,
                      b_ub=np.zeros(len(aug)), A_eq=np.array([[1.]*d+[0.]]),
                      b_eq=[1], bounds=[(0, None)]*(d+1), method="highs")
        if not res.success or res.x[-1] < 1e-8:
            return
        f = np.sign(U @ res.x[:d])
        allrows = f[:, None] * U - X
        balance = solve(allrows, np.r_[-1., np.zeros(d-1)])
        branches.append({"mixed_signs": signs, "positive_witness": res.x[:d].tolist(),
                         "max_min_coefficient": float(res.x[-1]),
                         "max_b0": float(balance.x[0]),
                         "b0_witness": balance.x.tolist()})
        print(json.dumps({"branches": len(branches), "calls": calls,
                          "max_b0": float(balance.x[0])}), flush=True)
        return
    i = mixed[depth]
    for s in (-1, 1):
        more = rows + [(s*U[i]-X[i]).tolist()]
        result = solve(more)
        if result.success:
            dfs(depth+1, more, signs+[s])

dfs(0, base.tolist(), [])
args.output.write_text(json.dumps({"warning": "Floating LP exploration, not an exact certificate",
    "n": n, "basis": record["basis"], "labels": g,
    "matrix_exact": [[str(T[i,j]) for j in range(d)] for i in range(d)],
    "mixed_rows": mixed, "calls": calls, "branches": branches}, indent=2)+"\n")
