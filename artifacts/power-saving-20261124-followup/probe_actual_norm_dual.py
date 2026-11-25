#!/usr/bin/env python3
"""Numerical actual-norm KKT audit of an inherited rational unit-contact center.

This is not an exact sign or local-optimality certificate. The inherited center
is approximate to a certified root; this script performs floating-point algebra.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np

ap = argparse.ArgumentParser()
ap.add_argument('--source', type=Path, required=True)
ap.add_argument('--output', type=Path, required=True)
args = ap.parse_args()
raw = args.source.read_bytes()
data = json.loads(raw)
n = data['n']
heads = data['heads']
q = n * heads
scale = 2 / float(data['gamma'])
center = np.array([int(v) / int(data['denominator']) for v in data['center']])
a = center[:q].reshape(n, heads)
b = center[q:].reshape(n, heads)
x = ((np.arange(2**n)[:, None] >> np.arange(n)) & 1).astype(float)
B = 1 + x @ b
values = scale * (x @ a) / B
imax = values.argmax(axis=0)
imin = values.argmin(axis=0)
upper = values[imax, np.arange(heads)]
lower = values[imin, np.arange(heads)]
upper_budget = 1 + upper.sum()
lower_budget = -1 - lower.sum()
branch = 1 if upper_budget >= lower_budget else -1
extrema = imax if branch == 1 else imin
gradient = np.zeros(2*q)
for h in range(heads):
    row = x[extrema[h]]
    den = B[extrema[h], h]
    value = values[extrema[h], h]
    gradient[np.arange(n)*heads+h] = branch * scale * row / den
    gradient[q+np.arange(n)*heads+h] = -branch * value * row / den
active = np.array(data['active_vertices'])
labels = np.array(data['active_labels'])
xj, bj, vj = x[active], B[active], values[active]
jacobian = np.c_[
    (scale*xj[:, :, None]/bj[:, None, :]).reshape(len(active), q),
    (-vj[:, None, :]*xj[:, :, None]/bj[:, None, :]).reshape(len(active), q)]
lagrange = np.linalg.solve((labels[:, None]*jacobian).T, gradient)
origin = branch - np.dot(lagrange, labels)
report = {
    'status': 'FLOATING_POINT_EXPLORATION_ONLY_NOT_PROOF',
    'source_branch': 'origin/ar/7485202da367',
    'source_path': 'artifacts/beyond-counting-bound/unit-minimum-certificate/data.json',
    'source_sha256': hashlib.sha256(raw).hexdigest(),
    'n': n, 'heads': heads,
    'head_maxima': upper.tolist(), 'head_maximizing_vertices': imax.tolist(),
    'head_minima': lower.tolist(), 'head_minimizing_vertices': imin.tolist(),
    'upper_interval_budget': float(upper_budget),
    'lower_interval_budget': float(lower_budget),
    'smooth_branch': int(branch),
    'minimum_nonorigin_multiplier': float(lagrange.min()),
    'maximum_nonorigin_multiplier': float(lagrange.max()),
    'negative_nonorigin_multiplier_count': int((lagrange < 0).sum()),
    'origin_multiplier': float(origin),
    'stationarity_residual': float(np.max(abs((labels[:, None]*jacobian).T@lagrange-gradient))),
    'nonorigin_multipliers': lagrange.tolist(),
}
args.output.write_text(json.dumps(report, indent=2)+'\n')
print({k:v for k,v in report.items() if k != 'nonorigin_multipliers'}, flush=True)
