#!/usr/bin/env python3
"""Independently verify exact failures of fixed weighted tangent dictionaries.

Only standard-library integer and rational arithmetic is used. Each branch
has a nonnegative rational annihilator, excluding strict parity signs even
when every scalar square-kernel residue and reciprocal correction varies.
No family-dependent or asymptotic impossibility is claimed.
"""
from fractions import Fraction
from itertools import permutations
from math import prod, factorial
import argparse
import json


def modular_rank(matrix, prime):
    a = [[value % prime for value in row] for row in matrix]
    rank = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inverse = pow(a[rank][col], -1, prime)
        a[rank] = [value * inverse % prime for value in a[rank]]
        for i in range(rank + 1, len(a)):
            coefficient = a[i][col]
            a[i] = [(value - coefficient * pivot_value) % prime
                    for value, pivot_value in zip(a[i], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def verify(item):
    k, h, q = item['dimension'], item['heads'], item['scale']
    n = 1 << k
    u, v = item['u'], item['v']
    assert len(u) == len(v) == h
    assert all(len(row) == k + 1 for row in u + v)
    seen = set()
    affine_features = []
    for x in range(n):
        bits = [1] + [(x >> i) & 1 for i in range(k)]
        den = [q + x + j + 1 for j in range(h)]
        multiplier = prod(d * d for d in den)
        affine_features.append([bit * multiplier // (d * d)
                                for bit in bits for d in den])
    assert modular_rank(affine_features, 65521) == n
    for cert in item['certificates']:
        perm = tuple(cert['permutation'])
        assert sorted(perm) == list(range(h)) and perm not in seen
        seen.add(perm)
        weights = [Fraction(value) for value in cert['weights']]
        assert len(weights) == n and all(value >= 0 for value in weights)
        assert sum(weights) == 1
        annihilator = [Fraction(0)] * (2 * h)
        for x, weight in enumerate(weights):
            bits = [1] + [(x >> i) & 1 for i in range(k)]
            den = [q + x + j + 1 for j in range(h)]
            multiplier = prod(d * d for d in den)
            difference = [sum(bit * (v[perm[j]][i] - u[j][i])
                              for i, bit in enumerate(bits)) for j in range(h)]
            row = [difference[j] * multiplier // den[j] ** 2 for j in range(h)]
            row += [multiplier // den[j] for j in range(h)]
            sign = 1 if x.bit_count() % 2 == 0 else -1
            annihilator = [total + sign * weight * value
                           for total, value in zip(annihilator, row)]
        assert all(value == 0 for value in annihilator)
    assert seen == set(permutations(range(h)))
    print(f'k={k}, H={h}: ambient affine feature rank {n}; '
          f'parity excluded in all {factorial(h)} weighted branches by exact rational certificates')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('certificate')
    args = parser.parse_args()
    with open(args.certificate) as source:
        for item in json.load(source):
            verify(item)
