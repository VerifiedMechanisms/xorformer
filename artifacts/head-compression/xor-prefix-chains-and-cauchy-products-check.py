#!/usr/bin/env python3
"""Exact finite tests for the written XOR-chain and Cauchy identities."""
from fractions import Fraction as F
from itertools import combinations
from math import comb
import json
import random

moments = 0
for q in range(1, 13):
    for k in range(1, q + 1):
        total = F(0)
        for marked in combinations(range(1, q + 1), k):
            endpoints = (0,) + marked + (q + 1,)
            gaps = [endpoints[i+1] - endpoints[i] for i in range(k+1)]
            value = F(sum((-1)**i * g for i, g in enumerate(gaps)), q+1)
            total += value * value
        actual = total / comb(q, k)
        expected = F(q-k, (q+1)*(k+2)) if k % 2 else F(q-k+1, (q+1)*(k+1))
        assert actual == expected and actual <= F(1, k+1)
        moments += 1

def prefixes(pi):
    out = [0]
    for j in pi:
        out.append(out[-1] ^ (1 << j))
    return out

def hat(values, mask):
    return sum((-1)**((x & mask).bit_count()) * weight for x, weight in values.items())

rng = random.Random(9135)
coverings = 0
for q in range(2, 9):
    chains = []
    for _ in range(q):
        pi = list(range(q)); rng.shuffle(pi)
        chains.append(prefixes(pi))
    distribution = {0: F(1)}
    for chain in chains:
        nxt = {}
        for x, weight in distribution.items():
            for y in chain:
                nxt[x ^ y] = nxt.get(x ^ y, F(0)) + weight / (q+1)
        distribution = nxt
    assert len(distribution) == 2**q
    for mask in range(2**q):
        product = F(1)
        for chain in chains:
            product *= hat({x:F(1,q+1) for x in chain}, mask)
        assert hat(distribution, mask) == product
    coverings += 1

schur_checks = 0
for size in range(1, 8):
    T = F(20)
    pivots = [F(j, 11) for j in range(1, size+1)]
    points = pivots + [F(9, 7), F(13, 9), F(19, 11)]
    matrix = [[1/(T-x-y) for y in points] for x in points]
    for step, a in enumerate(pivots):
        pivot = matrix[step][step]
        assert pivot > 0
        old = [row[:] for row in matrix]
        for i in range(step+1, len(points)):
            for j in range(step+1, len(points)):
                matrix[i][j] = old[i][j] - old[i][step]*old[step][j]/pivot
                x, y = points[i], points[j]
                expected = 1/(T-x-y)
                for b in pivots[:step+1]:
                    expected *= (x-b)*(y-b)/((T-x-b)*(T-b-y))
                assert matrix[i][j] == expected
                schur_checks += 1
print(json.dumps(dict(exact_second_moments=moments,
                      small_sumset_coverings=coverings,
                      exact_schur_entries=schur_checks)))
