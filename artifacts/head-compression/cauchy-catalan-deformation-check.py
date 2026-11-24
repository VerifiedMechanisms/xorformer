#!/usr/bin/env python3
"""Exact series and rank checks for cauchy-catalan-deformation.tex."""
from fractions import Fraction as F
from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path
from math import comb

spec = spec_from_file_location(
    "krylov", Path(__file__).with_name("cauchy-krylov-leading-audit-check.py"))
krylov = module_from_spec(spec)
spec.loader.exec_module(krylov)


def mul(a, b, length):
    return [sum((a[i] * b[k - i] for i in range(k + 1)
                 if i < len(a) and k - i < len(b)), F(0))
            for k in range(length)]


def inv(a, length):
    assert a[0]
    b = [1 / a[0]]
    for k in range(1, length):
        b.append(-sum((a[i] * b[k - i] for i in range(1, k + 1)
                       if i < len(a)), F(0)) / a[0])
    return b


def power(a, exponent, length):
    if exponent < 0:
        return power(inv(a, length), -exponent, length)
    out = [F(1)] + [F(0)] * (length - 1)
    for _ in range(exponent):
        out = mul(out, a, length)
    return out


def generalized_binomial(top, bottom):
    out = F(1)
    for i in range(bottom):
        out *= F(top - i, i + 1)
    return out


def coefficient_vectors(poles, weights, order):
    heads = len(poles)
    series = [[mul(weights[h], power(poles[h], j, order + 1), order + 1)
               for h in range(heads)] for j in range(order + 1)]
    return [[series[j][h][ell] for h in range(heads)]
            for ell in range(order + 1) for j in range(order + 1)]


def solve(matrix, target):
    a = [list(map(F, row)) + [F(value)] for row, value in zip(matrix, target)]
    size = len(a)
    for col in range(size):
        pivot = next(i for i in range(col, size) if a[i][col])
        a[col], a[pivot] = a[pivot], a[col]
        factor = a[col][col]
        a[col] = [value / factor for value in a[col]]
        for i in range(size):
            if i != col:
                factor = a[i][col]
                a[i] = [u - factor * v for u, v in zip(a[i], a[col])]
    return [row[-1] for row in a]


def main():
    checks = 0
    for q in range(2, 10):
        length = q + 3
        catalan = [F(comb(2 * k, k), k + 1) for k in range(length)]
        denominator = [F(1)] + [-2 * catalan[k - 1]
                                for k in range(1, length)]
        for r in range(-q, q + 1):
            series = mul(power(catalan, r, length), inv(denominator, length), length)
            for k in range(length):
                assert series[k] == generalized_binomial(2 * k + r, k)
                checks += 1
        w = mul(power(catalan, -(q - 1), length), inv(denominator, length), length)
        for j in range(q):
            series = mul(w, power(catalan, j, length), length)
            for ell in range(j, q):
                assert series[ell - j] == generalized_binomial(
                    2 * ell - j - q + 1, ell - j)
                if ell < q - 1 and 2 * ell - j >= q - 1:
                    assert not series[ell - j]
                if ell == q - 1:
                    assert series[ell - j] == 1
                checks += 1
        # Vandermonde independence of all preceding and final powers.
        nodes = list(map(F, range(1, 2 * q)))
        assert krylov.rank([[x ** d for x in nodes] for d in range(q - 1)]) == q - 1
        assert krylov.rank([[x ** d for x in nodes] for d in range(2 * q - 1)]) == 2 * q - 1
        target = [F(0)] * (q - 1) + [F((-1) ** k * (k + 1)) for k in range(q)]
        s = solve([[x ** d for x in nodes] for d in range(2 * q - 1)], target)
        for time in (F(2), F(7, 3)):
            output = [F(0)] * q
            for x, amplitude in zip(nodes, s):
                pole = [F(0)] + [x ** (2 * k + 1) * catalan[k] for k in range(q - 1)]
                weight = [x ** (2 * k) * w[k] for k in range(q)]
                denom = [time] + [-value for value in pole[1:]]
                score = mul(weight, inv(denom, q), q)
                output = [u + amplitude * v for u, v in zip(output, score)]
            assert output[:-1] == [F(0)] * (q - 1)
            assert output[-1] == sum(target[q - 1 + k] * time ** k
                                     for k in range(q)) / time ** q
            checks += q
    nodes = list(map(F, range(1, 6)))
    poles = [[F(0), x, x ** 4] for x in nodes]
    weights = [[F(1), x, x ** 3] for x in nodes]
    assert [krylov.rank(coefficient_vectors(poles, weights, order))
            for order in range(3)] == [1, 2, 5]
    nodes = list(map(F, range(1, 8)))
    poles = [[F(0), x, -x ** 3, 2 * x ** 5] for x in nodes]
    weights = [[F(1), x ** 2, F(0), x ** 6] for x in nodes]
    assert [krylov.rank(coefficient_vectors(poles, weights, order))
            for order in range(4)] == [1, 3, 3, 7]
    print(f"PASS: {checks} exact Catalan coefficients; q=2..9; both deformed-pole rank examples")


if __name__ == "__main__":
    main()
