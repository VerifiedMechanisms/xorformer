#!/usr/bin/env python3
"""Check the paired-root obstruction using rational arithmetic, no solver."""
import json
from fractions import Fraction as F
from pathlib import Path

path = Path(__file__).with_name("positive-paired-root-q5-dual.json")
data = json.loads(path.read_text())
q = data["q"]
p = list(map(F, data["poles"]))
delta = F(data["pair_shift"])
words = data["words"]
assert q == 5 and len(p) == q
assert all(0 <= p[r] < p[r] + delta < F(1, 2) for r in range(q))
assert all(p[r] + delta < p[r + 1] for r in range(q - 1))
assert words == [[1, -1, -1, 1, -1], [1, -1, 1, -1, 1]]

rows = []
order = []
for k, word in enumerate(words):
    for a in range(q):
        for b in range(q):
            if word[a] != 1 or word[b] != -1:
                continue
            sign = 1 if p[a] > p[b] else -1
            row = [F(sign * word[r]) / ((1-p[a]-p[r]) * (1-p[b]-p[r]))
                   for r in range(q)]
            row += [-F(sign * word[r]) /
                    ((1-p[a]-p[r]-delta) * (1-p[b]-p[r]-delta))
                    for r in range(q)]
            rows.append(row)
            order.append([k, a, b])
comparison_count = len(rows)
for r in range(2*q):
    rows.append([F(int(i == r)) for i in range(2*q)])
    order.append(["positive", r])
assert order == data["row_order"]
dual = list(map(F, data["dual"]))
assert len(dual) == len(rows)
assert all(x >= 0 for x in dual) and sum(dual) == 1
assert sum(dual[:comparison_count]) > 0
for j in range(2*q):
    assert sum(dual[i] * rows[i][j] for i in range(len(rows))) == 0
print(f"PASS: {comparison_count} comparisons, {2*q} nonnegativity rows, "
      f"{sum(x > 0 for x in dual)} nonzero dual coefficients")
