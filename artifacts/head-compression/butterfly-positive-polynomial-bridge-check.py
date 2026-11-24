#!/usr/bin/env python3
"""Check positive pair witnesses and one positive quadratic bridge obstruction.

Only exact rational arithmetic is used. The pole scale is fixed at 1/100;
this is not an asymptotic obstruction to a decoder or to HeadComplexity.
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import json
from flint import fmpq_mat as Matrix, fmpq as Q

path = Path(__file__).parent
data = json.loads((path / 'butterfly-positive-polynomial-bridge.json').read_text())
spec = importlib.util.spec_from_file_location('bf', path / 'butterfly-rectangle-decoder-check.py')
bf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bf)
d = data['dimension']
H = 1 << d
B = data['B']
eps = F(data['epsilon'])
switches = bf.switches(d)
blocks = list(dict.fromkeys((k, g) for k, s, g in switches))
poles = [sum((eps ** data['powers'][j] for j in range(d) if y & (1 << j)), F(0))
         for y in range(H)]


def comparisons(bits):
    permutation = bf.permutation(d, bits)
    inverse = [permutation.index(y) for y in range(H)]
    rows = []
    for k, g in blocks:
        positive = [s for e, (l, s, b) in enumerate(switches)
                    if (l, b) == (k, g) and bits[e] == 0]
        negative = [s for e, (l, s, b) in enumerate(switches)
                    if (l, b) == (k, g) and bits[e] == 1]
        for a in positive:
            for b in negative:
                sign = 1 if poles[a] > poles[b] else -1
                rows.append([F(sign * (0 if inverse[y] >> (k + 1) != g
                                      else 1 if not inverse[y] & (1 << k) else -1)) /
                             ((1 - poles[a] - poles[y]) * (1 - poles[b] - poles[y]))
                             for y in range(H)])
    return rows


base_rows = list(map(comparisons, data['targets']))
pair_checks = 0
seen_pairs = set()
for record in data['positive_pair_witnesses']:
    assert record['feasible']
    pair = tuple(record['pair'])
    seen_pairs.add(pair)
    point = list(map(F, record['witness']))
    assert len(point) == H and min(point) > 0
    for index in pair:
        for row in base_rows[index]:
            assert sum(a * b for a, b in zip(row, point)) > 0
            pair_checks += 1
assert seen_pairs == {(i, j) for i in range(4) for j in range(i + 1, 4)}

C = Matrix([[Q(str(1 / (1 - poles[i] - poles[j]))) for j in range(H)]
            for i in range(H)])
profiles = Matrix([[Q(str(poles[i] ** j)) for j in range(B)] for i in range(H)])
Vmat = C.inv() * profiles
assert C * Vmat == profiles
V = [[F(str(Vmat[i, j])) for j in range(B)] for i in range(H)]
rows, metadata = [], []
for index in data['left'] + data['right']:
    for ri, row in enumerate(base_rows[index]):
        rows.append(row + [sum(row[i] * V[i][j] for i in range(H))
                           if index in data['right'] else F(0) for j in range(B)])
        metadata.append(['cone', index, ri])
for j in range(H):
    rows.append([F(i == j) for i in range(H)] + [F(0)] * B)
    metadata.append(['positive_left', j])
for j in range(H):
    rows.append([F(i == j) for i in range(H)] + V[j])
    metadata.append(['positive_right', j])

dual = [F(0)] * len(rows)
for record in data['dual']:
    index = record['row']
    assert metadata[index] == record['kind'] and dual[index] == 0
    dual[index] = F(record['weight'])
assert min(dual) >= 0 and sum(dual) == 1
assert all(sum(dual[i] * rows[i][j] for i in range(len(rows))) == 0
           for j in range(H + B))
assert B == 3 and data['left'] == [0, 1] and data['right'] == [2, 3]
print(json.dumps(dict(dimension=d, positive_pair_intersections=6,
                      pair_comparisons=pair_checks, farkas_support=len(data['dual']),
                      positive_quadratic_bridge=False,
                      status='finite exact certificates, no asymptotic conclusion')))
