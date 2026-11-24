#!/usr/bin/env python3
"""Exact finite certificates for the written multiaffine entropy obstruction.

This is an abstract positive-parameter polynomial family, not an original
xorformer family. No capacity claim about original Boolean evaluations follows.
"""
from fractions import Fraction
from itertools import permutations
from math import factorial, gcd, lcm
import json


def elementary(values):
    out = [1] + [0] * len(values)
    for value in values:
        for k in range(len(values), 0, -1):
            out[k] += value * out[k - 1]
    return out


def solve(matrix, rhs):
    n = len(matrix)
    rows = [[Fraction(x) for x in row] + [Fraction(y)]
            for row, y in zip(matrix, rhs)]
    for col in range(n):
        pivot = next(i for i in range(col, n) if rows[i][col])
        rows[col], rows[pivot] = rows[pivot], rows[col]
        scale = rows[col][col]
        rows[col] = [x / scale for x in rows[col]]
        for i in range(n):
            if i != col:
                scale = rows[i][col]
                rows[i] = [x - scale * y for x, y in zip(rows[i], rows[col])]
    return [row[-1] for row in rows]


def certificate(size):
    assert size >= 2 and size & (size - 1) == 0
    bits = size.bit_length() - 1
    roots = list(range(1, size + 1))
    matrix = [elementary([j for j in roots if j != root]) for root in roots]
    coefficients, root_values = [], []
    for bit in range(bits):
        labels = [1 if ((root - 1) >> bit) & 1 else -1 for root in roots]
        coeff = solve(matrix, labels)
        denominator = lcm(*(c.denominator for c in coeff))
        integer_coeff = [int(c * denominator) for c in coeff]
        divisor = gcd(*integer_coeff)
        integer_coeff = [c // divisor for c in integer_coeff]
        values = [sum(a * b for a, b in zip(row, integer_coeff)) for row in matrix]
        assert all((v > 0) == (label > 0) for v, label in zip(values, labels))
        assert len(set(map(abs, values))) == 1
        coefficients.append(integer_coeff)
        root_values.append(values)
    result = {
        'size': size,
        'bits_per_position': bits,
        'variables': size,
        'evaluation_polynomials': size * bits,
        'coefficient_basis': 'e_0,...,e_(H-1) of all variables except position i',
        'integer_coefficients_by_bit': coefficients,
        'values_by_omitted_root': root_values,
        'all_root_values_exactly_checked': True,
    }
    if size <= 4:
        patterns = set()
        for perm in permutations(roots):
            pattern = []
            for i in range(size):
                es = elementary(perm[:i] + perm[i + 1:])
                for bit, coeff in enumerate(coefficients):
                    value = sum(a * b for a, b in zip(es, coeff))
                    actual = int(value > 0)
                    assert value != 0
                    assert actual == ((perm[i] - 1) >> bit) & 1
                    pattern.append(actual)
            patterns.add(tuple(pattern))
        assert len(patterns) == factorial(size)
        result['all_permutations_directly_evaluated'] = factorial(size)
        result['distinct_strict_sign_patterns'] = len(patterns)
    else:
        result['all_permutations_directly_evaluated'] = False
        result['distinct_patterns_from_written_injectivity_proof'] = factorial(size)
    return result


print(json.dumps({
    'status': 'finite exact computation, not a Lean theorem',
    'original_head_model': False,
    'cases': [certificate(4), certificate(8)],
}, indent=2))
