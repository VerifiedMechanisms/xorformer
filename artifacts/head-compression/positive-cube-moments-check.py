#!/usr/bin/env python3
"""Exact finite checks of positive-cube-moments.tex, not a proof by search."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import sympy as sp


def subsets(mask):
    x = mask
    while True:
        yield x
        if x == 0:
            break
        x = (x - 1) & mask


def laplace_product(rate, weights, mask):
    return sum(((-1) ** t.bit_count()) /
               (rate + sum(weights[i] for i in range(len(weights)) if t >> i & 1))
               for t in subsets(mask))


checks = {"mobius_coefficients": 0, "affine_moment_coefficients": 0,
          "log_supermodularity_pairs": 0, "fourier_resolvent_entries": 0,
          "odd_extension_entries": 0, "odd_extension_bounds": 0}
for n in range(1, 7):
    b0 = Q(3, 2)
    b = [Q(2 * i + 1, i + 2) for i in range(n)]
    a0 = Q(-5, 3)
    a = [Q((-1) ** i * (i + 2), i + 1) for i in range(n)]
    N = 1 << n
    vals = [(a0 + sum(a[i] for i in range(n) if t >> i & 1)) /
            (b0 + sum(b[i] for i in range(n) if t >> i & 1)) for t in range(N)]
    moments = [laplace_product(b0, b, s) for s in range(N)]
    for s in range(N):
        direct = sum((-1) ** (s.bit_count() - t.bit_count()) * vals[t]
                     for t in subsets(s))
        reciprocal = sum((-1) ** (s.bit_count() - t.bit_count()) /
                         (b0 + sum(b[i] for i in range(n) if t >> i & 1))
                         for t in subsets(s))
        assert reciprocal == (-1) ** s.bit_count() * moments[s]
        checks["mobius_coefficients"] += 1
        if s:
            rhs = sum((a0 * b[i] / b0 - a[i]) *
                      laplace_product(b0 + b[i], b, s ^ (1 << i))
                      for i in range(n) if s >> i & 1)
            assert (-1) ** s.bit_count() * direct == rhs
            checks["affine_moment_coefficients"] += 1
        for t in range(N):
            assert moments[s] * moments[t] <= moments[s & t] * moments[s | t]
            checks["log_supermodularity_pairs"] += 1
    w = [Q(i + 1, n * (n + 1)) for i in range(n)]
    tau = sum(w)
    L = sp.zeros(N)
    for s in range(N):
        for i in range(n):
            L[s, s ^ (1 << i)] += sp.Rational(w[i].numerator, w[i].denominator)
    vertices = list(product([-1, 1], repeat=n))
    values = [(a0 + sum(a[i] * x[i] for i in range(n))) /
              (1 - sum(w[i] * x[i] for i in range(n))) for x in vertices]
    def char(x, s):
        out = 1
        for i in range(n):
            if s >> i & 1:
                out *= x[i]
        return out
    fourier = sp.Matrix([sum(v * char(x, s) for x, v in zip(vertices, values)) / N
                         for s in range(N)])
    source = sp.zeros(N, 1)
    source[0] = a0
    for i in range(n):
        source[1 << i] = a[i]
    assert (sp.eye(N) - L) * fourier == source
    checks["fourier_resolvent_entries"] += N
    odd = [s for s in range(N) if s.bit_count() % 2]
    D = [s for s in odd if s.bit_count() == 1]
    E = [s for s in odd if s.bit_count() >= 3]
    if E:
        M = L * L
        P = (sp.eye(len(E)) - M.extract(E, E)).inv() * M.extract(E, D)
        assert all(v >= 0 for v in P)
        for row, s in enumerate(E):
            assert sum(P[row, j] for j in range(len(D))) <= tau ** (s.bit_count() - 1)
            checks["odd_extension_bounds"] += 1
        odd_values = [sum(a[i] * x[i] for i in range(n)) /
                      (1 - sum(w[i] * x[i] for i in range(n)) ** 2) for x in vertices]
        c = [sum(v * char(x, s) for x, v in zip(vertices, odd_values)) / N
             for s in range(N)]
        assert P * sp.Matrix([c[s] for s in D]) == sp.Matrix([c[s] for s in E])
        checks["odd_extension_entries"] += len(E)

out = {"status": "all exact rational checks passed", "checks": checks,
       "scope": "Finite checks only; general identities have written proofs. No asymptotic bound."}
path = Path(__file__).with_suffix(".json")
path.write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
