#!/usr/bin/env python3
"""Exact finite checks for butterfly-invariant-costs.tex.

Exhaustive covariance tests stop at H=8.  They check, and do not replace,
the written all-d proof. Run through heavy because all switch words are
enumerated. No floating point arithmetic is used.
"""
from fractions import Fraction as F
import importlib.util
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "butterfly", ROOT / "butterfly-rectangle-decoder-check.py")
bf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bf)

covariance_entries = 0
identity_entries = 0
for d in range(1, 4):
    H = 1 << d
    sw = bf.switches(d)
    input_haar = [(i, np.array([
        int(h >> (i + 1) == g) * (1 - 2 * ((h >> i) & 1))
        for h in range(H)], dtype=np.int64))
        for i in range(d) for g in range(H >> (i + 1))]
    output_haar = [(j, np.array([
        int(y % (1 << j) == s) * (1 - 2 * ((y >> j) & 1))
        for y in range(H)], dtype=np.int64))
        for j in range(d) for s in range(1 << j)]
    modes = [(i, j, u, v) for i, u in input_haar
             for j, v in output_haar]
    features = []
    for word in range(1 << len(sw)):
        bits = [(word >> e) & 1 for e in range(len(sw))]
        pi = list(bf.permutation(d, bits))
        features.append([int(u @ v[pi]) for i, j, u, v in modes])
    features = np.array(features, dtype=np.int64)
    assert np.all(features.sum(axis=0) == 0)
    gram = features.T @ features
    expected = np.zeros_like(gram)
    for k, (i, j, u, v) in enumerate(modes):
        factor = 0 if i > j else (2 if i == j else 1)
        numerator = len(features) * factor * int(u @ u) * int(v @ v)
        assert numerator % H == 0
        expected[k, k] = numerator // H
    assert np.array_equal(gram, expected)
    covariance_entries += len(modes) ** 2

    poles = [F(y + 1, 100 * H) for y in range(H)]
    q = [F((y * 7) % 11 - 5, 3) for y in range(H)]
    D0, D1, u, v = F(7, 5), F(9, 5), F(2, 3), F(-4, 7)
    a = [q[y] * (D0 - poles[y]) * (D1 - poles[y])
         + u * poles[y] + v for y in range(H)]
    for word in range(min(1 << len(sw), 128)):
        bits = [(word >> e) & 1 for e in range(len(sw))]
        pi = bf.permutation(d, bits)
        for mask in range(min(1 << H, 32)):
            alpha = [(mask >> h) & 1 for h in range(H)]
            D = [D0 if z else D1 for z in alpha]
            lhs = sum((a[pi[h]] - u * D[h] - v) /
                      (D[h] - poles[pi[h]]) for h in range(H))
            rhs = sum(q[y] * (D0 - poles[y]) for y in range(H)) - H * u
            rhs += (D1 - D0) * sum(alpha[h] * q[pi[h]] for h in range(H))
            assert lhs == rhs
            identity_entries += 1

paired_entries = 0
for k in range(1, 501):
    x, y = F(k, 10001), F(k + 501, 10001)
    m, c = F((7 * k) % 31 - 15, 11), F((13 * k) % 37 - 18, 7)
    D, E = F(3, 2) + F(k % 7, 20), F(3, 2) + F(k % 9, 20)
    b, e = F(k % 13, 5), F(-(k % 17), 3)
    S, P, T = x + y, x * y, m * x * y + c * (x + y)
    def delta(t, z):
        return (m * x + c + z) / (t - x) - (m * y + c + z) / (t - y)
    lhs = (D - x) * (D - y) * (E - x) * (E - y) / (x - y)
    lhs *= delta(D, b) - delta(E, e)
    rhs = ((D - E) * (T - D * E * m - (D + E) * c)
           + (e * D - b * E) * S + (b - e) * P + b * E * E - e * D * D)
    assert lhs == rhs
    paired_entries += 1

print(f"PASS: {covariance_entries} exact covariance entries; "
      f"{identity_entries} reciprocal identities; "
      f"{paired_entries} paired-output identities")
