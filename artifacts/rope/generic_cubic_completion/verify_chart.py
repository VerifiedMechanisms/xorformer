#!/usr/bin/env python3
"""Exact chart and interpolation constants for the fourteen-coordinate cubic.

This checks the coordinate map, a rational zero chart inside the cube, and
rank 679 of the degree-three graph-restriction map over a finite field.
It does not by itself prove a finite Boolean separation.
"""

from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import factorial, isqrt


def inverse(matrix):
    size = len(matrix)
    a = [row[:] + [F(i == j) for j in range(size)]
         for i, row in enumerate(matrix)]
    for j in range(size):
        pivot = next(i for i in range(j, size) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        a[j] = [value / a[j][j] for value in a[j]]
        for i in range(size):
            if i != j:
                value = a[i][j]
                a[i] = [x - value * y for x, y in zip(a[i], a[j])]
    assert all(a[i][j] == (i == j) for i in range(size) for j in range(size))
    return [row[size:] for row in a]


def multiply(a, b, prime):
    result = {}
    for i, x in a.items():
        for j, y in b.items():
            result[i + j] = (result.get(i + j, 0) + x * y) % prime
    return {i: x for i, x in result.items() if x}


def graph_rank():
    # Monomials in thirteen variables are encoded in base ten. No variable
    # exponent reaches ten, so addition of codes is multiplication of monomials.
    prime = 1000000007
    assert all(prime % d for d in range(2, isqrt(prime) + 1))
    one = {0: 1}
    x = [{10**i: 1} for i in range(13)]
    plus = lambda i: {0: 1, 10**i: 1}
    d = multiply(plus(3), plus(4), prime)
    first = multiply(x[0], plus(4), prime)
    second = multiply(x[1], plus(3), prime)
    total = first.copy()
    for key, value in second.items():
        total[key] = (total.get(key, 0) + value) % prime
    numerator = {key: -value % prime for key, value in
                 multiply(plus(2), total, prime).items()}
    d_power, n_power = [one], [one]
    for _ in range(3):
        d_power.append(multiply(d_power[-1], d, prime))
        n_power.append(multiply(n_power[-1], numerator, prime))
    base = [multiply(n_power[a], d_power[3 - a], prime) for a in range(4)]
    pivots = {}
    columns = 0
    max_exponent = 0
    for degree in range(4):
        for indices in combinations_with_replacement(range(14), degree):
            exponent = indices.count(0)
            shift = sum(10**(i - 1) for i in indices if i)
            row = {key + shift: value for key, value in base[exponent].items()}
            for code in row:
                max_exponent = max(max_exponent, *(int(c) for c in str(code)))
            columns += 1
            while row:
                pivot = min(row)
                if pivot not in pivots:
                    scale = pow(row[pivot], prime - 2, prime)
                    pivots[pivot] = {key: value * scale % prime
                                     for key, value in row.items()}
                    break
                scale = row[pivot]
                for key, value in pivots[pivot].items():
                    new = (row.get(key, 0) - scale * value) % prime
                    if new:
                        row[key] = new
                    else:
                        row.pop(key, None)
    assert columns == 680
    assert len(pivots) == 679
    assert max_exponent <= 9
    return len(pivots), max_exponent


def cleared_coefficients(matrix):
    def times(a, b):
        result = {}
        for i, x in a.items():
            for j, y in b.items():
                key = tuple(sorted(i + j))
                result[key] = result.get(key, F(0)) + x * y
        return result
    s = [{(i,): value for i, value in enumerate(matrix[h])} for h in range(3)]
    d = [{(): F(1), **{(i,): value for i, value in enumerate(matrix[h + 3])}}
         for h in range(3)]
    result = {}
    for h in range(3):
        p, q = [j for j in range(3) if j != h]
        for key, value in times(times(s[h], d[p]), d[q]).items():
            result[key] = result.get(key, F(0)) + value
    return {key: value for key, value in result.items() if value}


def main():
    size = 14
    matrix = [[F(i**h, 10000) for i in range(1, size + 1)] for h in range(3)]
    matrix += [[(F(i)**(h + 3) - F(15, 2)**(h + 3)) / 10**9
                for i in range(1, size + 1)] for h in range(3)]
    matrix += [[F(i == j) for j in range(size)] for i in range(6, size)]
    inv = inverse(matrix)
    assert all(48 % value.denominator == 0 for row in inv for value in row)
    norm = max(sum(abs(value) for value in row) for row in inv)
    assert norm == F(93456593389, 8) < 2**34
    assert max(sum(abs(value) for value in row) for row in matrix) == 1
    coefficients = cleared_coefficients(matrix)
    coefficient_norm = max(abs(value) for value in coefficients.values())
    gradient_bound = sum(len(key) * abs(value) for key, value in coefficients.items())
    all_positive_value = sum(coefficients.values())
    assert coefficient_norm < 1
    assert gradient_bound < 1 < 2040
    assert all_positive_value > F(1, 10) > F(1, 10000)
    assert max(abs(row[0]) for row in inv) < 2**24
    # Every free chart coordinate is j/L, with j in {0,...,9}. The dependent
    # coordinate is -(1+B0)(S1/(1+B1)+S2/(1+B2)).
    length = 10 * 2**40
    radius = F(1, 2**40)
    assert F(9, length) < radius
    dependent_bound = (1 + radius) * 2 * radius / (1 - radius)
    assert dependent_bound < 3 * radius
    assert 3 * radius * norm < F(3, 64) < F(1, 16)
    for j1 in range(10):
        for j2 in range(10):
            denominator = 48 * length * (length + j1) * (length + j2)
            assert denominator < 2**138
            # This single denominator clears all original coordinates for
            # every choice of the other eleven grid indices.
            assert denominator % (48 * length) == 0
            dependent = -(1 + F(9, length)) * (
                F(9, length) / (1 + F(j1, length)) +
                F(9, length) / (1 + F(j2, length)))
            assert (denominator * dependent / 48).denominator == 1
    # A nonzero 679-square evaluation determinant is at least 2^(-414*679).
    # All entries have magnitude <=1. The adjugate/cofactor estimate below
    # bounds every inverse row sum, without choosing the independent rows.
    assert factorial(679) * 2**(414 * 679) < 2**300000
    rank, degree = graph_rank()
    print({'inverse_denominator': 48, 'inverse_norm': str(norm),
           'chart_grid_denominator': length, 'point_denominator_power_bound': 138,
           'evaluation_rank': rank, 'max_free_variable_degree': degree,
           'inverse_minor_norm_power_bound': 300000,
           'cleared_coefficient_norm': str(coefficient_norm),
           'cleared_gradient_bound': str(gradient_bound),
           'cleared_at_all_positive': str(all_positive_value)})


if __name__ == '__main__':
    main()
