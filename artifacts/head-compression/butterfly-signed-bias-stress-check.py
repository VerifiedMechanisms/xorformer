#!/usr/bin/env python3
"""Exact stress-word certificates, with and without legal block biases.

No feasibility solver is used. Requires python-flint. A guarded Laurent
solve certifies the signs of exact rational-function leading coefficients.
"""
from pathlib import Path
from fractions import Fraction as F
import importlib.util, json, sys
from flint import fmpq_mat, fmpq_series as S, ctx
sys.set_int_max_str_digits(0)
path = Path(__file__).parent
spec = importlib.util.spec_from_file_location('bf', path/'butterfly-rectangle-decoder-check.py')
bf = importlib.util.module_from_spec(spec); spec.loader.exec_module(bf)


def matrix(data, z, zero, one, biased):
    d = data['d']; H = 1 << d; sw = bf.switches(d)
    bits = data.get('target', data.get('bits'))
    assert bits == [(s >> max(0, k-1)) & 1 for k, s, g in sw]
    pi = bf.permutation(d, bits); inv = [pi.index(y) for y in range(H)]
    poles = [sum((z**pw for j, pw in enumerate(data['powers']) if y & (1 << j)), zero)
             for y in range(H)]
    blocks = sorted(set((k, g) for k, s, g in sw))
    rows = []
    for e, (k, s, g) in enumerate(sw):
        sign = 1-2*bits[e]
        row = [zero if inv[y] >> (k+1) != g else
               sign * (1 if not inv[y] & (1 << k) else -1)/(one-poles[s]-poles[y])
               for y in range(H)]
        if biased: row += [sign*one if b == (k, g) else zero for b in blocks]
        rows.append(row)
    return rows


def guarded_solve(A, rhs, precision):
    n = len(A); assert all(len(row) == n for row in A)
    T = [row[:] + [b] for row, b in zip(A, rhs)]
    cols = list(range(n)); pivots = []
    for k in range(n):
        candidates = [(T[i][j].valuation(), i, j) for i in range(k, n)
                      for j in range(k, n) if T[i][j].valuation() >= 0]
        assert candidates
        val, i, j = min(candidates)
        assert all(T[ii][jj].valuation() >= 0 or T[ii][jj].prec >= val
                   for ii in range(k, n) for jj in range(k, n))
        pivots.append(val); T[k], T[i] = T[i], T[k]
        for row in T: row[k], row[j] = row[j], row[k]
        cols[k], cols[j] = cols[j], cols[k]; pivot = T[k][k]
        assert all(v.prec >= val if v.valuation() < 0 else v.valuation() >= val for v in T[k])
        T[k] = [v/pivot for v in T[k]]
        for i in range(n):
            if i != k:
                mult = T[i][k]
                if mult.valuation() >= 0:
                    T[i] = [a-mult*b for a, b in zip(T[i], T[k])]
                else:
                    # A truncated zero is O(x^prec), not an exact zero.
                    # All pivot-row entries have nonnegative valuation.
                    T[i] = [S(a, prec=min(a.prec, mult.prec)) for a in T[i]]
    solution = [None]*n
    for i in range(n): solution[cols[i]] = T[i][-1]
    for row, b in zip(A, rhs):
        residual = sum((a*c for a, c in zip(row, solution)), S([]))-b
        assert residual.valuation() < 0 and residual.prec > precision//3
    return solution, pivots


data = json.loads((path/'butterfly-signed-unbiased-h16-dual.json').read_text())
H = 1 << data['d']; A = matrix(data, F(data['epsilon']), F(0), F(1), False)
support = [i for i, value in data['dual']]; weights = [F(value) for i, value in data['dual']]
assert len(support) == H+1 and all(i < len(A) for i in support)
assert min(weights) > 0 and sum(weights) == 1
assert all(sum(w*A[i][j] for i, w in zip(support, weights)) == 0 for j in range(H))
K = data['precision']; ctx.cap = K; M = K//3; x = S([0, 1]); A = matrix(data, x, S([]), S([1]), False)
B = [[A[i][j] for i in support] for j in range(H)] + [[S([1])]*(H+1)]
sol, pivots = guarded_solve(B, [S([])]*H+[x**M], K)
leading = []
for i, v in zip(support, sol):
    order = v.valuation(); assert order >= 0 and v[order] > 0
    leading.append([i, order-M, str(v[order])])
assert data['laurent'] == dict(support=support, pivots=pivots, leading=leading)
print('PASS: signed unbiased H16 is infeasible at epsilon=1/100 and for all sufficiently small epsilon', flush=True)

file = path/'butterfly-signed-biased-h32-germ.json'
assert file.exists()
data = json.loads(file.read_text()); H = 1 << data['d']; D = 2*H-1
A = matrix(data, F(data['epsilon']), F(0), F(1), True); count = len(A)
A += [[F(i == j) for j in range(D)] for i in range(D)]
basis = data['basis']; assert len(basis) == D
B = fmpq_mat([[str(v) for v in A[tag]] for tag, rhs in basis])
c = B.solve(fmpq_mat([[rhs] for tag, rhs in basis]))
values = [F(str(c[i, 0])) for i in range(D)]
assert all(sum(a*b for a, b in zip(row, values)) >= 1 for row in A[:count])
assert sum(v < 0 for v in values[:H]) == 18
K = data['precision']; ctx.cap = K; M = K//3; x = S([0, 1])
A = matrix(data, x, S([]), S([1]), True)
A += [[S([int(i == j)]) for j in range(D)] for i in range(D)]
sol, pivots = guarded_solve([A[tag] for tag, rhs in basis], [rhs*x**M for tag, rhs in basis], K)
leading = []
for i, row in enumerate(A[:count]):
    score = sum((a*b for a, b in zip(row, sol)), S([])); order = score.valuation()
    assert order >= 0 and score[order] > 0
    leading.append([i, order-M, str(score[order])])
assert data['laurent'] == dict(pivots=pivots, leading=leading)
print('PASS: signed biased H32 realizes all 80 stress-word signs at epsilon=1/100 and for all sufficiently small epsilon')
