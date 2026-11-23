#!/usr/bin/env python3
"""Exact finite histogram fibers; no asymptotic sign-coverage claim.

Run with ``heavy python3 reciprocal-histogram-fibers-check.py``.
The large-fiber theorem is proved in the companion TeX file, not by this
enumeration. These checks include the mixed-projection obstruction to
combining separate one-triple collisions.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import permutations, product
import json

PRIME = 1_000_003

STATES = ((0, 0), (1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1))


def signature(perms, h):
    k = len(perms)
    # A negative direction contains exactly the reflected multiset.
    directions = (v for v in product(STATES, repeat=k)
                  if next((z for ab in v for z in ab if z), 1) > 0)
    return tuple(tuple(sorted(sum(i * a + p[i] * b
                                  for p, (a, b) in zip(perms, v))
                              for i in range(h))) for v in directions)


def denominator(perms, h, index, x):
    k = len(perms)
    common = 1 + (h + 1) * (sum(x[:3 * k]) + sum(
        (2 ** j) * bit for j, bit in enumerate(x[3 * k:])))
    return common + sum(
        index * (x[3 * ell] - x[3 * ell + 1])
        + p[index] * (x[3 * ell + 1] - x[3 * ell + 2])
        for ell, p in enumerate(perms))


def check_fiber(fiber, h, n):
    coefficients = set()
    for perms in fiber:
        rows = []
        for index in range(h):
            slopes = [h + 1] * (3 * len(perms)) + [
                (h + 1) * 2 ** j for j in range(n - 3 * len(perms))]
            for ell, p in enumerate(perms):
                slopes[3 * ell] += index
                slopes[3 * ell + 1] += p[index] - index
                slopes[3 * ell + 2] -= p[index]
            assert min(slopes) >= 2
            rows.append(tuple(slopes))
        coefficients.add(tuple(sorted(rows)))
    assert len(coefficients) == len(fiber)
    for x in product((0, 1), repeat=n):
        tables = [[denominator(p, h, i, x) for i in range(h)] for p in fiber]
        assert min(min(ds) for ds in tables) > 0
        assert all(sorted(ds) == sorted(tables[0]) for ds in tables)
        values = [sum((Fraction(1, d) for d in ds), Fraction(0)) for ds in tables]
        assert all(value == values[0] for value in values)


def determinant_mod(matrix):
    matrix = [row[:] for row in matrix]
    result = 1
    for j in range(len(matrix)):
        pivot = next((i for i in range(j, len(matrix)) if matrix[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            result = -result
        value = matrix[j][j]
        result = result * value % PRIME
        inverse = pow(value, -1, PRIME)
        for i in range(j + 1, len(matrix)):
            factor = matrix[i][j] * inverse % PRIME
            matrix[i] = [(v - factor * w) % PRIME
                         for v, w in zip(matrix[i], matrix[j])]
    return result % PRIME


def check_restricted_regular(perms, h):
    k = len(perms)
    m = (h - 1).bit_length()
    matrix = []
    for block in range(k + 1):
        core = [0] * (3 * k)
        if block == 0:
            core[0] = 1
        else:
            core[3 * (block - 1)] = core[3 * (block - 1) + 1] = 1
        for number in range(h):
            x = core + [(number >> j) & 1 for j in range(m)]
            inverse_squares = [(-pow(denominator(perms, h, i, x), -2, PRIME)) % PRIME
                               for i in range(h)]
            row = inverse_squares[:]
            for ell in range(k):
                b = x[3 * ell + 1] - x[3 * ell + 2]
                row += [(b * v) % PRIME for v in inverse_squares]
            matrix.append(row)
    determinant = determinant_mod(matrix)
    assert determinant != 0
    return determinant


def tangent_space_mod(perms, h):
    """Canonical row basis of the transpose of the full-cube Jacobian."""
    k = len(perms)
    n = 3 * k + (h - 1).bit_length()
    outputs = []
    for x in product((0, 1), repeat=n):
        inverse_squares = [(-pow(denominator(perms, h, i, x), -2, PRIME)) % PRIME
                           for i in range(h)]
        row = inverse_squares[:]
        for ell in range(k):
            b = x[3 * ell + 1] - x[3 * ell + 2]
            row += [(b * v) % PRIME for v in inverse_squares]
        outputs.append(row)
    matrix = [list(col) for col in zip(*outputs)]
    rank = 0
    for column in range(len(outputs)):
        pivot = next((j for j in range(rank, len(matrix)) if matrix[j][column]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][column], -1, PRIME)
        matrix[rank] = [(v * inverse) % PRIME for v in matrix[rank]]
        for j in range(len(matrix)):
            if j != rank:
                factor = matrix[j][column]
                matrix[j] = [(v - factor * w) % PRIME
                             for v, w in zip(matrix[j], matrix[rank])]
        rank += 1
        if rank == len(matrix):
            break
    assert rank == (k + 1) * h
    return tuple(tuple(row) for row in matrix)


def main():
    expected = {(3, 1): 2, (4, 1): 3, (5, 1): 6, (6, 1): 12,
                (7, 1): 28, (8, 1): 76, (3, 2): 1, (4, 2): 1, (5, 2): 1}
    for (h, k), size in expected.items():
        ps = list(permutations(range(h)))
        groups = defaultdict(list)
        for perms in product(ps, repeat=k):
            groups[signature(perms, h)].append(perms)
        fiber = max(groups.values(), key=len)
        assert len(fiber) == size
        check_fiber(fiber, h, max(5, 3 * k))
        determinants = [check_restricted_regular(p, h) for p in fiber]
        tangent_spaces = {tangent_space_mod(p, h) for p in fiber}
        assert len(tangent_spaces) == len(fiber)
        print(json.dumps({"H": h, "k": k, "representations": len(ps) ** k,
                          "fibers": len(groups), "largest_fiber": len(fiber),
                          "full_cube_exact_check": True,
                          "strict_positive_slopes": True,
                          "restricted_regular_dimension": (k + 1) * h,
                          "nonzero_modular_determinants": len(determinants),
                          "distinct_full_cube_tangent_spaces": len(tangent_spaces),
                          "asymptotic_sign_bound_proved": False}), flush=True)


if __name__ == "__main__":
    assert all(PRIME % d for d in range(2, 1001))
    main()
