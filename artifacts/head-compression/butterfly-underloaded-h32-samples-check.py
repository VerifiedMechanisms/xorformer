#!/usr/bin/env python3
"""Exact finite underloaded-H32 samples; no solver and no universality claim."""
import importlib.util
import json
import sys
from fractions import Fraction as F
from pathlib import Path
from flint import fmpq_mat

sys.set_int_max_str_digits(0)

path = Path(__file__).resolve().parent
data = json.loads((path / 'butterfly-underloaded-h32-samples.json').read_text())
spec = importlib.util.spec_from_file_location('bf', path / 'butterfly-rectangle-decoder-check.py')
bf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bf)
d = data['d']
H = 1 << d
switches = bf.switches(d)
eps = F(data['epsilon'])
p = [sum((eps ** data['powers'][j] for j in range(d) if y & (1 << j)), F(0))
     for y in range(H)]
selected = [e for e, (k, s, g) in enumerate(switches) if s < (1 << k) - 1]
assert selected == data['selected'] and len(selected) == 49
checked = 0
for cert in data['certificates']:
    bits = cert['bits']
    assert all(bits[e] == 0 for e in range(len(switches)) if e not in selected)
    pi = bf.permutation(d, bits)
    inv = [pi.index(y) for y in range(H)]
    rows = {}
    for e in selected:
        k, s, g = switches[e]
        rows[e] = [F((1 - 2 * bits[e]) *
                     (0 if inv[y] >> (k + 1) != g else
                      1 if not inv[y] & (1 << k) else -1)) / (1 - p[s] - p[y])
                   for y in range(H)]
    rows.update({len(switches) + i: [F(int(i == j)) for j in range(H)]
                 for i in range(H)})
    assert len(cert['basis']) == H and len(set(cert['basis'])) == H
    B = fmpq_mat([[str(a) for a in rows[e]] for e in cert['basis']])
    solution = B.solve(fmpq_mat([[1] for _ in range(H)]))
    c = [F(str(solution[i, 0])) for i in range(H)]
    assert all(sum(a * b for a, b in zip(row, c)) >= 1 for row in rows.values())
    checked += len(rows)
assert len(data['certificates']) == 20
print(f'PASS: 20 finite H32 words, {checked} exact strict score/positivity checks; no universality assertion.')
