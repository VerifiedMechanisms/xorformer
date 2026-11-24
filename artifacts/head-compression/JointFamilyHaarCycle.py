#!/usr/bin/env python3
"""Exact obstruction to one proposed incidence factorization of Haar readouts.

This uses only integer and rational arithmetic. It does not disprove the Haar
sign decoder, and does not establish a lower bound on head complexity.
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

BITS = [1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1]
CYCLE = [0, 0, 0, 0, 1, -1, -1, 1, 1, -1, -1, 1]
ORDER = 4


def add(a, b):
    return [a[i] + b[i] for i in range(ORDER)]


def scale(c, a):
    return [c * x for x in a]


def mul(a, b):
    return [sum(a[j] * b[i-j] for j in range(i+1)) for i in range(ORDER)]


def inverse_unit(a):
    assert a[0] == 1
    b = [1] + [0] * (ORDER-1)
    for i in range(1, ORDER):
        b[i] = -sum(a[j] * b[i-j] for j in range(1, i+1))
    return b


def monomial(degree):
    return [int(i == degree) for i in range(ORDER)]


def main():
    d, H, eps = 3, 8, F(1, 100)
    switches = butterfly.switches(d)
    permutation = butterfly.permutation(d, BITS)
    blocks = list(dict.fromkeys((k, g) for k, s, g in switches))
    positions = list(range(H))
    incidence, biases, coefficients = [], [], []
    gamma = [eps ** (2**k) for k in range(d)]
    poles = [sum((gamma[k] for k in range(d) if y >> k & 1), F(0))
             for y in range(H)]
    series_gamma = [monomial(2**k) for k in range(d)]
    series_poles = [[sum(series_gamma[k][r] for k in range(d) if y >> k & 1)
                     for r in range(ORDER)] for y in range(H)]
    series_cycle = [0] * ORDER
    for index, (k, s, g) in enumerate(switches):
        wire0 = s + (g << (k+1))
        wire1 = wire0 + (1 << k)
        h0, h1 = positions[wire0], positions[wire1]
        row = [0] * H
        row[h0], row[h1] = -1, 1
        incidence.append(row)
        biases.append([int(block == (k, g)) for block in blocks])
        D, G = 1-poles[s], gamma[k]
        coefficients.append([
            F((1-2*((h >> k) & 1)) if h >> (k+1) == g else 0)
            * G / ((D-poles[permutation[h]]) * (D+G-poles[permutation[h]]))
            for h in range(H)])
        # The residue column h=0 has Haar weight one exactly when g=0.
        if CYCLE[index] and g == 0:
            den = add(monomial(0), scale(-1, add(series_poles[s],
                                               series_poles[permutation[0]])))
            den2 = add(den, series_gamma[k])
            term = mul(series_gamma[k], mul(inverse_unit(den), inverse_unit(den2)))
            series_cycle = add(series_cycle, scale(CYCLE[index], term))
        if BITS[index]:
            positions[wire0], positions[wire1] = positions[wire1], positions[wire0]
    assert all(sum(CYCLE[e]*incidence[e][h] for e in range(len(switches))) == 0
               for h in range(H))
    assert all(sum(CYCLE[e]*biases[e][b] for e in range(len(switches))) == 0
               for b in range(len(blocks)))
    value = sum((CYCLE[e]*coefficients[e][0] for e in range(len(switches))), F(0))
    assert value < 0
    assert series_cycle == [0, 0, 0, -2]
    result = dict(d=d, bits=BITS, switches=switches, cycle=CYCLE,
                  residue_column=0, epsilon=str(eps), rational_value=str(value),
                  taylor_coefficients_through_degree_three=series_cycle,
                  incidence_annihilated=True, block_biases_annihilated=True,
                  scope="excludes A = B T + Z C; does not exclude Haar sign feasibility")
    print(json.dumps(result, separators=(",", ":")))


if __name__ == "__main__":
    main()
