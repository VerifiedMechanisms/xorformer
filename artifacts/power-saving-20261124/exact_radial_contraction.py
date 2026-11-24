#!/usr/bin/env python3
"""Construct an exact Farkas certificate for a discovered contraction loss."""
import json
from pathlib import Path
import time

import sympy as sp

ROOT = Path(__file__).resolve().parent
t = sp.Symbol("t")
started = time.monotonic()
data = json.loads((ROOT / "radial_contraction_discovery.json").read_text())
r = data["results"][-1]
slopes = r["slopes"]
labels = r["labels"]
rows = []
denoms = []
for v in range(16):
    x = [(v >> i) & 1 for i in range(4)]
    d = [1 + t * sum(a * b for a, b in zip(x, s)) for s in slopes]
    denoms.append(d)
    rows.append([d[0] * d[1]] + [xi * d[1] for xi in x] + [xi * d[0] for xi in x])
M = sp.Matrix(rows)
coeff = sp.Matrix([sp.Rational(str(v)).limit_denominator(100000)
                   for v in r["large_coefficients"]])
vals = M.subs(t, 1) * coeff
assert all(labels[i] * vals[i] > 0 for i in range(16))
support = [i for i, v in enumerate(r["small_dual"]) if v > 1e-6]
print("support", support, "coefficients", list(coeff), flush=True)
signed = sp.Matrix([[labels[i] * M[i, j] for i in support] for j in range(M.cols)])
null = signed.nullspace()
print("symbolic_nullity", len(null), "elapsed", time.monotonic()-started, flush=True)
assert len(null) == 1
vec = [sp.factor(v) for v in null[0]]
small = sp.Rational(1, 1000)
if any(v.subs(t, small) < 0 for v in vec):
    vec = [-v for v in vec]
assert all(v.subs(t, small) > 0 for v in vec)
for i, v in zip(support, vec):
    print(i, sp.factor(v), flush=True)
    assert sp.limit(v, t, 0, dir="+") >= 0
assert all(sp.cancel(v) == 0 for v in signed * sp.Matrix(vec))
payload = {"status": "exact symbolic annihilation; positive interval to be audited",
           "slopes": slopes, "labels": labels,
           "large_coefficients": [str(v) for v in coeff],
           "large_cleared_values": [str(v) for v in vals],
           "dual_support": support, "dual_rational_functions": [str(v) for v in vec],
           "elapsed_seconds": time.monotonic()-started}
(ROOT / "radial_contraction_exact.json").write_text(json.dumps(payload, indent=2)+"\n")
