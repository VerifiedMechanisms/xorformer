#!/usr/bin/env python3
"""Exact checks for butterfly-biased-dual-audit.tex; no universality claim."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util
import random

spec = importlib.util.spec_from_file_location(
    "bf", Path(__file__).with_name("butterfly-rectangle-decoder-check.py"))
bf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bf)
rng = random.Random(20261124)
paired = differences = inverse_entries = 0


def prod(values):
    ans = F(1)
    for value in values:
        ans *= value
    return ans


for q in range(1, 9):
    xs = [F(i * i, 10 * q * q) for i in range(q)]
    C = [[1 / (1 - x - y) for y in xs] for x in xs]
    inv = [[
        prod(1 - xs[i] - x for x in xs)
        * prod(1 - xs[j] - x for x in xs)
        / ((1 - xs[i] - xs[j])
           * prod(xs[i] - xs[k] for k in range(q) if k != i)
           * prod(xs[j] - xs[k] for k in range(q) if k != j))
        for j in range(q)] for i in range(q)]
    for i in range(q):
        for j in range(q):
            assert sum(C[i][k] * inv[k][j] for k in range(q)) == (i == j)
            inverse_entries += 1

for d in range(1, 4):
    H = 1 << d
    switches = bf.switches(d)
    blocks = list(dict.fromkeys((k, g) for k, s, g in switches))
    eta = [F(1, 100) ** (2 ** j) for j in range(d)]
    poles = [sum((eta[j] for j in range(d) if y & (1 << j)), F(0))
             for y in range(H)]
    settings = (list(product((0, 1), repeat=len(switches))) if d < 3 else
                [tuple(rng.randrange(2) for _ in switches) for _ in range(257)])
    for bits in settings:
        pi = bf.permutation(d, bits)
        v = {}
        for k, g in blocks:
            a = [F(rng.randrange(-9, 10), 11) for _ in range((1 << k) - 1)]
            v[k, g] = a + [-sum(a)]

        def u(block, h):
            k, g = block
            return (1 - 2 * ((h >> k) & 1)) if h >> (k + 1) == g else 0

        def R(block, x):
            return sum((a / (1 - poles[s] - x)
                        for s, a in enumerate(v[block])), F(0))

        residual = [sum((u(block, h) * R(block, poles[pi[h]])
                         for block in blocks), F(0)) for h in range(H)]
        for k, s, g in switches:
            hs = [[h for h in range(H)
                   if h >> (k + 1) == g and ((h >> k) & 1) == bit
                   and pi[h] % (1 << k) == s] for bit in range(2)]
            assert len(hs[0]) == len(hs[1]) == 1
            h0, h1 = hs[0][0], hs[1][0]
            x0, x1 = poles[pi[h0]], poles[pi[h1]]
            rhs = R((k, g), x0) + R((k, g), x1)
            for block in blocks:
                if block[0] < k:
                    rhs += u(block, h0) * R(block, x0) - u(block, h1) * R(block, x1)
                elif block[0] > k:
                    assert u(block, h0) == u(block, h1)
                    rhs += u(block, h0) * (R(block, x0) - R(block, x1))
            assert rhs == residual[h0] - residual[h1]
            tail = sum(eta[k:])
            assert 0 <= x0 - poles[s] <= tail and 0 <= x1 - poles[s] <= tail
            paired += 1

        c = [F(rng.randrange(-9, 10), 13) for _ in range(H)]
        for k, g in blocks:
            for a in range(1 << k):
                for b in range(a):
                    original = sum((u((k, g), h) * c[pi[h]]
                                    * (1 / (1 - poles[a] - poles[pi[h]])
                                       - 1 / (1 - poles[b] - poles[pi[h]]))
                                    for h in range(H)), F(0))
                    reduced = (poles[a] - poles[b]) * sum((
                        u((k, g), h) * c[pi[h]]
                        / ((1 - poles[a] - poles[pi[h]])
                           * (1 - poles[b] - poles[pi[h]]))
                        for h in range(H)), F(0))
                    assert original == reduced
                    differences += 1

print(f"PASS: {paired} paired-leaf identities, {differences} bias differences, "
      f"{inverse_entries} inverse-Cauchy entries; no all-level feasibility claim.")
