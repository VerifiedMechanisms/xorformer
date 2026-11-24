#!/usr/bin/env python3
"""Exact failure of one switch-cone quadratic positivity criterion.

This is an elementary rational/power-series calculation. It is not a Haar
infeasibility certificate and is not a lower bound on head complexity.
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import json

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "butterfly", HERE / "butterfly-rectangle-decoder-check.py")
butterfly = importlib.util.module_from_spec(spec)
spec.loader.exec_module(butterfly)

BITS = [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1]
MU = [0, 0, 0, 0, 36, 0, -36, 0, 81, -112, 45, -14]
ORDER = 5


def add(a, b):
    return [x+y for x, y in zip(a, b)]


def scale(c, a):
    return [c*x for x in a]


def mul(a, b):
    return [sum(a[j]*b[i-j] for j in range(i+1)) for i in range(ORDER)]


def inverse_unit(a):
    assert a[0] == 1
    b = [1] + [0]*(ORDER-1)
    for i in range(1, ORDER):
        b[i] = -sum(a[j]*b[i-j] for j in range(1, i+1))
    return b


def monomial(i):
    return [int(i == j) for j in range(ORDER)]


def mask(h, k, g):
    return (1-2*((h >> k) & 1)) if h >> (k+1) == g else 0


def main():
    d, H, eps = 3, 8, F(1, 100)
    switches = butterfly.switches(d)
    permutation = butterfly.permutation(d, BITS)
    blocks = list(dict.fromkeys((k, g) for k, s, g in switches))
    assert all(MU[e]*(1-2*BITS[e]) >= 0 for e in range(len(switches)))
    assert all(sum(MU[e] for e, (k, s, g) in enumerate(switches)
                   if (k, g) == block) == 0 for block in blocks)
    positions, incidence = list(range(H)), []
    for e, (k, s, g) in enumerate(switches):
        i, j = s+(g << (k+1)), s+(g << (k+1))+(1 << k)
        row = [0]*H
        row[positions[i]], row[positions[j]] = 1, -1
        incidence.append(row)
        if BITS[e]:
            positions[i], positions[j] = positions[j], positions[i]
    alpha = [sum(MU[e]*incidence[e][h] for e in range(len(switches)))
             for h in range(H)]
    gamma = [monomial(2**k) for k in range(d)]
    poles = [[sum(gamma[k][j] for k in range(d) if y >> k & 1)
              for j in range(ORDER)] for y in range(H)]
    raw, normalized = [0]*ORDER, [0]*ORDER
    for e, (k, s, g) in enumerate(switches):
        for h in range(H):
            weight = MU[e]*mask(h, k, g)*alpha[h]
            denominator = add(monomial(0), scale(-1, add(poles[s], poles[permutation[h]])))
            denominator2 = add(denominator, gamma[k])
            term = scale(weight, mul(inverse_unit(denominator), inverse_unit(denominator2)))
            normalized = add(normalized, term)
            raw = add(raw, mul(gamma[k], term))
    assert raw == [0, 0, 0, -9648, -20088]
    assert normalized == [0, -9648, 170424, 708192, 2439588]
    rational_gamma = [eps**(2**k) for k in range(d)]
    rational_poles = [sum((rational_gamma[k] for k in range(d) if y >> k & 1), F(0))
                      for y in range(H)]
    raw_value, normalized_value = F(0), F(0)
    dual_residual = [F(0)]*H
    for e, (k, s, g) in enumerate(switches):
        D = 1-rational_poles[s]
        for h in range(H):
            denominator = D-rational_poles[permutation[h]]
            assert denominator > 0
            coefficient = F(mask(h, k, g))/(denominator*(denominator+rational_gamma[k]))
            normalized_value += MU[e]*coefficient*alpha[h]
            raw_value += MU[e]*rational_gamma[k]*coefficient*alpha[h]
            dual_residual[h] += MU[e]*rational_gamma[k]*coefficient
    assert raw_value < 0 and normalized_value < 0
    assert any(dual_residual)  # This is deliberately NOT a Farkas certificate.
    result = dict(d=d, bits=BITS, switches=switches, mu=MU,
                  incidence_transpose_mu=alpha, epsilon=str(eps),
                  raw_coefficients=raw, normalized_coefficients=normalized,
                  raw_value=str(raw_value), normalized_value=str(normalized_value),
                  block_sums_zero=True, in_desired_switch_cone=True,
                  dual_residual_nonzero=True,
                  scope="excludes direct A B^T switch-cone positivity, not Haar feasibility")
    print(json.dumps(result, separators=(",", ":")))


if __name__ == "__main__":
    main()
