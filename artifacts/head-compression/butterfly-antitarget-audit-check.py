#!/usr/bin/env python3
"""Exact anti-target routing audit. No feasibility solver is used."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import json, importlib.util, sys, random
from flint import fmpq_mat, fmpq_series as S, ctx
sys.set_int_max_str_digits(0)
path = Path(__file__).parent
data = json.loads((path / 'butterfly-antitarget-audit.json').read_text())
spec = importlib.util.spec_from_file_location('bf', path / 'butterfly-rectangle-decoder-check.py')
bf = importlib.util.module_from_spec(spec); spec.loader.exec_module(bf)


def rows(d, target, z, zero, one):
    H = 1 << d; sw = bf.switches(d)
    poles = [sum((z**(2**j) for j in range(d) if y & (1 << j)), zero) for y in range(H)]
    pi = bf.permutation(d, [1-b for b in target]); inv = [pi.index(y) for y in range(H)]
    A = [[zero if inv[y] >> (k+1) != g else
          (1-2*target[e]) * (1 if not inv[y] & (1 << k) else -1)
          / (one-poles[s]-poles[y]) for y in range(H)]
         for e, (k, s, g) in enumerate(sw)]
    return A + [[one if i == j else zero for j in range(H)] for i in range(H)]


count = 0
for key in ('h8', 'h16'):
    block = data[key]; d = block['d']; H = 1 << d; sw = bf.switches(d)
    assert all(z['sat'] for z in block['records'])
    for record in block['records']:
        A = rows(d, record['target'], F(block['epsilon']), F(0), F(1))
        basis = record['basis']; assert len(basis) == H
        c = fmpq_mat([[str(a) for a in A[i]] for i in basis]).solve(fmpq_mat([[1]]*H))
        c = [F(str(c[i, 0])) for i in range(H)]
        assert all(sum(a*b for a, b in zip(row, c)) >= 1 for row in A)
        count += len(A)
        if d == 3:
            bottom = [e for e, (k, _, _) in enumerate(sw) if k == 0]
            for low in product((0, 1), repeat=len(bottom)):
                target = record['target'][:]
                for e, b in zip(bottom, low): target[e] = b
                assert rows(d, target, F(block['epsilon']), F(0), F(1)) == A
    if d == 3:
        upper = [e for e, (k, _, _) in enumerate(sw) if k > 0]
        assert len({tuple(z['target'][e] for e in upper) for z in block['records']}) == 256

# Audit the input-complement conjugacy independently of the samples.
rg = random.Random(9183)
for d in range(1, 7):
    H = 1 << d; sw = bf.switches(d); index = {v: e for e, v in enumerate(sw)}
    for _ in range(10):
        target = [rg.randrange(2) for _ in sw]
        relabeled = [target[index[k, s, g ^ ((1 << (d-k-1))-1)]] for k, s, g in sw]
        anti = bf.permutation(d, [1-b for b in target])
        direct = bf.permutation(d, relabeled)
        assert all(anti[h] == direct[h ^ (H-1)] for h in range(H))

# The first H16 target is the previously saved positive direct-routing obstruction.
old = json.loads((path / 'butterfly-adaptive-haar-positive-h16-dual.json').read_text())
record = data['h16']['records'][0]
assert record['target'] == old['bits']
d = 4; H = 16; K = data['h16_precision']; ctx.cap = K; M = K//3; x = S([0, 1])
A = rows(d, record['target'], x, S([]), S([1])); basis = record['basis']
original = [A[i] for i in basis]
T = [row[:] + [x**M] for row in original]; columns = list(range(H)); pivots = []
for k in range(H):
    candidates = [(T[i][j].valuation(), i, j) for i in range(k, H)
                  for j in range(k, H) if T[i][j].valuation() >= 0]
    assert candidates
    val, i, j = min(candidates); pivots.append(val)
    assert all(T[ii][jj].valuation() >= 0 or T[ii][jj].prec >= val
               for ii in range(k, H) for jj in range(k, H))
    T[k], T[i] = T[i], T[k]
    for row in T: row[k], row[j] = row[j], row[k]
    columns[k], columns[j] = columns[j], columns[k]
    pivot = T[k][k]
    assert all(z.prec >= val if z.valuation() < 0 else z.valuation() >= val for z in T[k])
    T[k] = [z/pivot for z in T[k]]
    for i in range(H):
        if i != k:
            mult = T[i][k]; T[i] = [a-mult*b for a, b in zip(T[i], T[k])]
c = [None]*H
for i in range(H): c[columns[i]] = T[i][-1]
for row in original:
    residual = sum((a*b for a, b in zip(row, c)), S([]))-x**M
    assert residual.valuation() < 0 and residual.prec > M
leading = []
for e, row in enumerate(A):
    value = sum((a*b for a, b in zip(row, c)), S([])); val = value.valuation()
    assert val >= 0 and value[val] > 0
    leading.append([e, val-M, str(value[val])])
assert dict(number=0, pivots=pivots, allpositive=True, leading=leading) == data['h16_laurent']
print(f'PASS: {count} finite score/residue inequalities; all4096 H8 target words; '
      '60 routing conjugacies; positive H16 repair for every sufficiently small epsilon')
