#!/usr/bin/env python3
"""Exact rational audit of the nonvertical affine-plane reverse decoder.

This verifies a concrete q=8, k=3 instance.  The identity being tested is
symbolic in the table columns; the test uses eight nonconstant columns.
"""

from fractions import Fraction as Q
import json
import sympy as sp


def mul(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= 0b1011
    return result


def inv(a):
    assert a
    return next(b for b in range(1, 8) if mul(a, b) == 1)


def main():
    q, k, s = 8, 3, 8
    points = [(x, y) for x in range(q) for y in range(q)]
    rows = [(h, b) for h in points for b in range(k)]
    delta, tau = Q(1, 8 * len(rows)), Q(1, 8 * s)
    poles = [1 - delta * Q(a + 1, q + 1) for a in range(q)]
    tokens = [tau * Q(z + 1, q + 1) for z in range(q)]
    cauchy = sp.Matrix([[sp.Rational(1 / (poles[a] - tokens[z]))
                         for a in range(q)] for z in range(q)])
    coefficients = []
    for b in range(k):
        target = sp.Matrix([1 if (z >> b) & 1 else -1 for z in range(q)])
        eta = cauchy.inv() * target
        assert cauchy * eta == target
        coefficients.append([Q(v.p, v.q) for v in eta])

    states = {(g, j): (mul(g[0], j) ^ g[1] ^ j)
              for g in points for j in range(s)}
    line_values = {}
    for a in range(q):
        for intercept in range(q):
            members = [g for g in points if g[1] == (mul(a, g[0]) ^ intercept)]
            assert len(members) == q
            for j in range(s):
                line_values[a, intercept, j] = sum(
                    (1 / (poles[a] - tokens[states[g, j]]) for g in members), Q(0))

    checked = 0
    for h, b in rows:
        for j in range(s):
            rank_term = sum((coefficients[b][a] *
                             line_values[a, h[1] ^ mul(a, h[0]), j]
                             for a in range(q)), Q(0))
            correction = Q(0)
            for g in points:
                if g[0] != h[0]:
                    slope = mul(g[1] ^ h[1], inv(g[0] ^ h[0]))
                    assert g[1] == (mul(slope, g[0]) ^ h[1] ^ mul(slope, h[0]))
                    correction += coefficients[b][slope] / (
                        poles[slope] - tokens[states[g, j]])
            target = 1 if (states[h, j] >> b) & 1 else -1
            assert rank_term - correction == target
            checked += 1

    # Each correction head has row poles among `poles` and column tokens
    # among `tokens`.  Its minimum on the whole cube is therefore bounded
    # below by this common exact margin, including rows with zero numerator.
    denominator_margin = 1 - len(rows) * delta - s * tau
    assert denominator_margin == Q(3, 4)
    print(json.dumps({"q": q, "rows": len(rows), "columns": s,
                      "exact_grid_equalities": checked,
                      "raw_head_budget": 2 * q * q + 1,
                      "correction_denominator_lower_bound": str(denominator_margin),
                      "interpolation": "exact rational, all token bits",
                      "status": "passed"}, indent=2))


if __name__ == "__main__":
    main()
