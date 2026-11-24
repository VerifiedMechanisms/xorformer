#!/usr/bin/env python3
"""Exact finite and small-scale obstruction to two positive root words.

No optimization solver is used. Rational comparison rows are reconstructed
from the saved words. Guarded power-series elimination verifies that a
normalized rational-function Farkas vector has positive leading terms.
"""
from pathlib import Path
from fractions import Fraction as F
import json
from flint import fmpq_series as S, ctx

data = json.loads(Path(__file__).with_name(
    "positive-paired-root-h16-dual.json").read_text())
words = data["words"]
assert words == [[1, 1, 1, 1, -1, -1, -1, -1],
                 [1, -1, 1, 1, -1, -1, 1, 1]]
q, n = 8, 16

def build_rows(p, delta, zero, one):
    rows, descriptions = [], []
    for k, word in enumerate(words):
        for a in range(q):
            for b in range(q):
                if word[a] != 1 or word[b] != -1:
                    continue
                j = next(j for j in range(3) if ((a >> j) & 1) != ((b >> j) & 1))
                sign = 1 if (a >> j) & 1 else -1
                row = [sign * word[r] /
                       ((1-p[a]-p[r]) * (1-p[b]-p[r])) for r in range(q)]
                row += [-sign * word[r] /
                        ((1-p[a]-p[r]-delta) * (1-p[b]-p[r]-delta))
                        for r in range(q)]
                rows.append(row)
                descriptions.append([k, a, b])
    assert len(rows) == data["comparison_count"] == 31
    for r in range(n):
        rows.append([one if j == r else zero for j in range(n)])
        descriptions.append(["positive", r])
    return rows, descriptions

epsilon = F(data["epsilon"])
assert 0 < epsilon <= F(1, 4)
p = [sum((epsilon**(1 << j) for j in range(3) if y >> j & 1), F(0))
     for y in range(q)]
assert max(p) + epsilon**8 < F(1, 2)
rows, descriptions = build_rows(p, epsilon**8, F(0), F(1))
weights = list(map(F, data["dual"]))
assert len(weights) == len(rows)
assert all(z >= 0 for z in weights) and sum(weights) == 1
assert sum(weights[:31]) > 0
assert all(sum(weights[i] * rows[i][j] for i in range(len(rows))) == 0
           for j in range(n))
support = [i for i, z in enumerate(weights) if z]
assert support == data["support"] and len(support) == n + 1

# Each formal entry is a rational function regular at zero. Choosing the
# least-valuation pivot and guarding every truncated zero ensures every
# displayed leading coefficient agrees with rational-function elimination.
ctx.cap = data["precision"]
shift = ctx.cap // 3
x = S([0, 1])
p = [sum((x**(1 << j) for j in range(3) if y >> j & 1), S([]))
     for y in range(q)]
rows, descriptions = build_rows(p, x**8, S([]), S([1]))
J = len(support)
basis = [[rows[i][j] for i in support] for j in range(n)] + [[S([1])]*J]
rhs = [S([])]*n + [x**shift]
aug = [row[:] + [value] for row, value in zip(basis, rhs)]
columns, pivots = list(range(J)), []
for k in range(J):
    valuation, i, j = min((aug[i][j].valuation(), i, j)
                         for i in range(k, J) for j in range(k, J)
                         if aug[i][j].valuation() >= 0)
    assert all(aug[ii][jj].valuation() >= 0 or aug[ii][jj].prec >= valuation
               for ii in range(k, J) for jj in range(k, J))
    pivots.append(valuation)
    aug[k], aug[i] = aug[i], aug[k]
    for row in aug:
        row[k], row[j] = row[j], row[k]
    columns[k], columns[j] = columns[j], columns[k]
    pivot = aug[k][k]
    assert all(z.prec >= valuation if z.valuation() < 0
               else z.valuation() >= valuation for z in aug[k])
    aug[k] = [z / pivot for z in aug[k]]
    for i in range(J):
        if i != k:
            multiplier = aug[i][k]
            aug[i] = [a - multiplier*b for a, b in zip(aug[i], aug[k])]
solution = [None]*J
for i in range(J):
    solution[columns[i]] = aug[i][-1]
for row, value in zip(basis, rhs):
    residual = sum((a*b for a, b in zip(row, solution)), S([])) - value
    assert residual.valuation() < 0 and residual.prec > 0
leading = []
for z in solution:
    valuation = z.valuation()
    assert 0 <= valuation < z.prec and z[valuation] > 0
    leading.append([valuation-shift, str(z[valuation])])
assert pivots == data["pivots"] and leading == data["leading"]
assert any(i < 31 for i in support)
print(json.dumps({"comparisons": 31, "dual_support": len(support),
                  "pivots": pivots, "leading": leading,
                  "status": "No shared nonnegative pool at epsilon=1/100 "
                            "or at any sufficiently small positive epsilon"}))
