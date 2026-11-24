#!/usr/bin/env python3
"""Exact finite checks for identical ratio-order branches and a boundary face."""
from fractions import Fraction
import contextlib
import io
import json
import runpy
from pathlib import Path

with contextlib.redirect_stdout(io.StringIO()):
    data = runpy.run_path(str(Path(__file__).with_name('check_generic_one_head_basis.py')))
X, T, I, G, dot = [data[k] for k in ('X', 'T', 'I', 'G', 'dot')]
B = [[34, 67, 48, 72, 39, 95, 60, 43], [23, 39, 4, 21, 37, 27, 96, 30]]
A = [[-2420, 4983, -3550, 5406, -2423, -1641, 778, -3137],
     [-1285, 2867, -2128, 3173, -1483, -993, 384, -1778]]
orders, labels = [], []
for a, b in zip(A, B):
    assert all(v > 0 for v in b)
    assert a == [dot(row, b) for row in T]
    assert all(abs(dot(x, a)) >= dot(x, b) for x in X)
    assert all(Fraction(dot(X[i], a), dot(X[i], b)) == g for i, g in zip(I, G))
    ratios = [Fraction(u, v) for u, v in zip(a, b)]
    assert len(set(ratios)) == 8
    orders.append(sorted(range(8), key=ratios.__getitem__))
    labels.append([dot(x, a) > 0 for x in X])
assert orders[0] == orders[1] == [2, 7, 0, 4, 5, 6, 1, 3]
disagreement = [i for i in range(128) if labels[0][i] != labels[1][i]]
assert disagreement == [17]
b = [0, 1, 0, 0, 0, 0, 0, 0]
a = [dot(row, b) for row in T]
assert a == [-6, 13, -10, 14, -6, -4, 2, -8]
assert all(abs(dot(x, a)) >= dot(x, b) for x in X)
face_values = [dot(x, a) for x in X if x[1] == 0]
assert min(face_values) < 0 < max(face_values)
print(json.dumps({'strict_ratio_order': orders[0], 'disagreement': disagreement,
                  'boundary_denominator': b, 'boundary_numerator': a,
                  'boundary_face_min': min(face_values),
                  'boundary_face_max': max(face_values)}, indent=2))
