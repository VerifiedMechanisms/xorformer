#!/usr/bin/env python3
"""Exact finite and guarded Laurent witness for the signed H32 stress word.

No feasibility solver is used. Requires python-flint.
"""
from pathlib import Path
from fractions import Fraction as F
import json, importlib.util, sys
from flint import fmpq_series as S, fmpq_mat, ctx
sys.set_int_max_str_digits(0)
path = Path(__file__).parent
data = json.loads((path / 'butterfly-underloaded-h32-signed.json').read_text())
spec = importlib.util.spec_from_file_location('bf', path / 'butterfly-rectangle-decoder-check.py')
bf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bf)
d = data['d']; H = 1 << d; sw = bf.switches(d)
bits = data['bits']; powers = data['powers']; pi = bf.permutation(d, bits)
inv = [pi.index(y) for y in range(H)]
assert data['selected'] == [e for e, (k, s, g) in enumerate(sw) if s < 2**k - 1]
assert bits == [((s >> max(0, k-1)) & 1) if e in data['selected'] else 0
                for e, (k, s, g) in enumerate(sw)]


def matrix(z, zero, one):
    poles = [sum((z**powers[j] for j in range(d) if y & (1 << j)), zero) for y in range(H)]
    rows = []
    for e, (k, s, g) in enumerate(sw):
        rows.append([zero if inv[y] >> (k+1) != g else
                     (1 - 2*bits[e]) * (1 if not inv[y] & (1 << k) else -1)
                     / (one - poles[s] - poles[y]) for y in range(H)])
    rows += [[one if i == j else zero for j in range(H)] for i in range(H)]
    return rows


finite = matrix(F(data['epsilon']), F(0), F(1))
basis = data['basis']
assert len(basis) == H and all(tag in data['selected'] or tag >= len(sw) for tag, _ in basis)
B = fmpq_mat([[str(a) for a in finite[tag]] for tag, _ in basis])
v = B.solve(fmpq_mat([[rhs] for _, rhs in basis]))
c = [F(str(v[i, 0])) for i in range(H)]
assert all(sum(a*b for a, b in zip(finite[e], c)) >= 1 for e in data['selected'])
assert sum(a < 0 for a in c) == 10

K = data['precision']; ctx.cap = K; M = K // 3; x = S([0, 1])
A = matrix(x, S([]), S([1]))
original = [A[tag] for tag, _ in basis]
rhs = [value*x**M for _, value in basis]
T = [row[:] + [b] for row, b in zip(original, rhs)]
cols = list(range(H)); pivots = []
for k in range(H):
    candidates = [(T[i][j].valuation(), i, j) for i in range(k, H)
                  for j in range(k, H) if T[i][j].valuation() >= 0]
    assert candidates
    val, i, j = min(candidates)
    assert all(T[ii][jj].valuation() >= 0 or T[ii][jj].prec >= val
               for ii in range(k, H) for jj in range(k, H))
    pivots.append(val); T[k], T[i] = T[i], T[k]
    for row in T: row[k], row[j] = row[j], row[k]
    cols[k], cols[j] = cols[j], cols[k]
    pivot = T[k][k]
    assert all(z.prec >= val if z.valuation() < 0 else z.valuation() >= val for z in T[k])
    T[k] = [z / pivot for z in T[k]]
    for i in range(H):
        if i != k:
            mult = T[i][k]
            T[i] = [a - mult*b for a, b in zip(T[i], T[k])]
solution = [None] * H
for i in range(H): solution[cols[i]] = T[i][-1]
for row, b in zip(original, rhs):
    residual = sum((a*c for a, c in zip(row, solution)), S([])) - b
    assert residual.valuation() < 0 and residual.prec > M
leading = []
for e in data['selected']:
    score = sum((a*c for a, c in zip(A[e], solution)), S([]))
    val = score.valuation()
    assert val >= 0 and score[val] > 0
    leading.append([e, val-M, str(score[val])])
assert dict(number=0, pivots=pivots, allpositive=True, leading=leading) == data['laurent']
print('PASS: 49 exact finite signed scores and 49 positive Laurent leading scores; '
      'the same fixed routing is feasible for every sufficiently small positive epsilon')
