#!/usr/bin/env python3
"""Verify an exact finite obstruction to an auxiliary SPD routing lemma.

Uses only Python integers. This is not a Lean theorem and is not an obstruction
to Cauchy blocks, the full tangent decoder, or the original attention model.
"""
import json
from pathlib import Path

path = Path(__file__).with_name('LargeDomainSPDPreconditioner.json')
data = json.loads(path.read_text())
d = data['d']
H = 1 << d
switches = [(k, s, g) for k in range(d)
            for s in range(1 << k) for g in range(1 << (d-k-1))]
bits = data['bits']
assert len(bits) == len(switches) and set(bits) <= {0, 1}
mu = [0] * len(switches)
for item in data['dual']:
    e, value = item['row'], int(item['coefficient'])
    assert 0 <= e < len(mu) and mu[e] == 0 and value > 0
    mu[e] = value
assert sum(mu) > 0

# B records the pair of original input wires at each switch, before that switch.
position = list(range(H))
edges = []
for bit, (k, s, g) in zip(bits, switches):
    left = s + (g << (k+1))
    right = left + (1 << k)
    edges.append((position[left], position[right]))
    if bit:
        position[left], position[right] = position[right], position[left]

# The desired sign is + for an unswitched comparator and - for a switched one.
# Every listed block K=R R^T+I is SPD since v^T K v=||R^T v||^2+||v||^2.
blocks = {(item['k'], item['g']): item['R'] for item in data['gram_blocks']}
assert len(blocks) == len(data['gram_blocks'])
residue_dual = [0] * H
for k in range(d):
    for g in range(1 << (d-k-1)):
        es = [e for e, (level, s, group) in enumerate(switches)
              if (level, group) == (k, g)]
        signed = [(1-2*bits[e])*mu[e] for e in es]
        # This is exactly the dual coefficient of the free bias at this node.
        assert sum(signed) == 0
        transformed = signed.copy()
        if (k, g) in blocks:
            R = blocks[k, g]
            assert len(R) == len(es) and all(len(row) == len(es) for row in R)
            assert all(type(value) is int for row in R for value in row)
            rt = [sum(R[i][j]*signed[i] for i in range(len(es)))
                  for j in range(len(es))]
            transformed = [signed[i]+sum(R[i][j]*rt[j] for j in range(len(es)))
                           for i in range(len(es))]
        for e, value in zip(es, transformed):
            left, right = edges[e]
            residue_dual[left] += value
            residue_dual[right] -= value
assert residue_dual == [0]*H
print(f'PASS: H={H}, {len(switches)} strict comparisons, '
      f'{len(data["dual"])} positive integer dual coefficients, '
      f'{len(blocks)} Gram-plus-identity blocks.')
print('The positive weighted sum of all requested strict inequalities is exactly 0.')
