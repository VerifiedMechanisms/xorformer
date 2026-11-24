#!/usr/bin/env python3
"""Exact finite check of the integer-fiber singular-jet identity.

This checks formal coefficients, original-atom positivity, and the resulting
strict signs for one nonconstant readout on every fiber.  It is an audit of
the written general proof, not a replacement for that proof or a Lean proof.
"""

from fractions import Fraction as F
from itertools import product
from math import prod


def lagrange_value(nodes, values, z):
    return sum(
        value * prod((z - node) / (nodes[i] - node)
                     for j, node in enumerate(nodes) if j != i)
        for i, value in enumerate(values)
    )


def audit():
    weights = [1, 1]
    r = 1 + sum(weights)
    kmax = 2
    heads = (2 * kmax + 1) * r - kmax
    nodes = [1 - F(t, 4 * r) for t in range(r)]
    poles = [F(h + 1, 8 * heads) for h in range(heads)]
    qprime = [prod(lam - other for j, other in enumerate(poles) if j != h)
              for h, lam in enumerate(poles)]
    pzero = lambda z: prod(z - d for d in nodes)
    pprime = [prod(d - other for j, other in enumerate(nodes) if j != t)
              for t, d in enumerate(nodes)]
    # Coefficients in the order constant, x_0, x_1.
    readouts = [[F(1), F(1), F(-2)],
                [F(-1), F(3), F(1)],
                [F(2), F(-2), F(1)]]
    polynomials = [[F(1), F(-2), F(3)],
                   [F(-2), F(1), F(1)],
                   [F(3), F(-1), F(-1)]]
    head_readouts = [
        [lagrange_value(nodes, [row[c] for row in readouts], lam)
         for c in range(3)]
        for lam in poles
    ]
    aj_at_poles = [
        [lagrange_value(nodes,
                        [polynomials[t][j] / pprime[t] ** j for t in range(r)],
                        lam)
         for j in range(kmax + 1)]
        for lam in poles
    ]
    # P_epsilon(lambda_h) coefficients indexed by epsilon degree.
    residue_coeffs = [
        [aj_at_poles[h][kmax - e] * pzero(poles[h]) ** (kmax - e)
         / qprime[h]
         for e in range(kmax + 1)]
        for h in range(heads)
    ]
    epsilon = F(1, 10 ** 8)
    rows = []
    for x in product((0, 1), repeat=len(weights)):
        t = sum(w * bit for w, bit in zip(weights, x))
        d = nodes[t]
        lx = readouts[t][0] + sum(a * bit for a, bit in zip(readouts[t][1:], x))
        target = sum(a * lx ** j for j, a in enumerate(polynomials[t]))
        assert target != 0
        qd = prod(d - lam for lam in poles)
        coeffs = [F(0) for _ in range(kmax + 1)]
        score = F(0)
        for h, lam in enumerate(poles):
            lh = head_readouts[h][0] + sum(a * bit for a, bit in zip(head_readouts[h][1:], x))
            base = d - lam
            for degree in range(kmax + 1):
                coeffs[degree] += sum(
                    residue_coeffs[h][e] * (-lh) ** (degree - e)
                    / base ** (degree - e + 1)
                    for e in range(degree + 1)
                )
            residue = sum(a * epsilon ** e for e, a in enumerate(residue_coeffs[h]))
            score += residue / (base + epsilon * lh)
        assert coeffs[:-1] == [0] * kmax
        assert coeffs[-1] == target / qd
        assert score * target > 0
        rows.append((x, t, target))

    # Check the same original atom parameters used in the written proof.
    for h, lam in enumerate(poles):
        intercept = 1 - lam + epsilon * head_readouts[h][0]
        slopes = [F(w, 4 * r) - epsilon * a
                  for w, a in zip(weights, head_readouts[h][1:])]
        gamma = intercept - 2 * sum(slopes)
        assert gamma > 0 and all(a > 0 for a in slopes)
        for x in product((0, 1), repeat=len(weights)):
            atom_denominator = gamma + sum(2 * a * F(1, 2) ** bit
                                           for a, bit in zip(slopes, x))
            expected = intercept - sum(a * bit for a, bit in zip(slopes, x))
            assert atom_denominator == expected and expected > 0

    print(f"PASS: R={r}, K={kmax}, H={heads}; exact coefficients through order K")
    print("PASS: original strict admissibility and strict signs at epsilon=1/10^8")
    for x, t, target in rows:
        print(f"  x={x}, fiber={t}, requested readout={target}")


if __name__ == "__main__":
    audit()
