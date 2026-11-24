#!/usr/bin/env python3
"""Exact replay of the separator obstruction, without altering Lean sources."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parent
points = [
    (Q(t*t-1, 1+t+t*t)+2, Q(-t*(t+2), 1+t+t*t)+2)
    for t in range(4, 11)
]
residues = [9030651, -139451671, 773603110, -2053378830,
            2822318335, -1938507571, 526385976]


def line(p, q):
    return (p[1]-q[1], q[0]-p[0], p[0]*q[1]-q[0]*p[1])


def evaluate(coeff, p):
    return coeff[0]*p[0]+coeff[1]*p[1]+coeff[2]


separators = []
for target in range(7):
    other = [i for i in range(7) if i != target]
    factors = [line(points[other[j]], points[other[j+1]])
               for j in range(0, 6, 2)]
    values = []
    for p in points:
        value = Q(1)
        for factor in factors:
            value *= evaluate(factor, p)
        values.append(value)
    assert values[target] != 0
    normalized = [v/values[target] for v in values]
    assert normalized == [Q(i == target) for i in range(7)]
    separators.append({
        'target': target,
        'line_factors': [[str(c) for c in f] for f in factors],
        'normalizer': str(values[target]),
        'evaluations': [str(v) for v in normalized],
    })

checks = 0
for x in [(0, 0), (1, 0), (0, 1), (1, 1)]:
    for degree in range(4):
        assert sum(c*(p[0]*x[0]+p[1]*x[1])**degree
                   for c, p in zip(residues, points)) == 0
        checks += 1
mixed_moment = sum(c*p[0]**2*p[1] for c, p in zip(residues, points))
assert mixed_moment != 0
assert all(p[0] > 0 and p[1] > 0 for p in points)
for x in [(1, 0), (0, 1), (1, 1)]:
    assert len({p[0]*x[0]+p[1]*x[1] for p in points}) == 7

result = {
    'status': 'PASS',
    'restricted_moment_checks': checks,
    'separator_evaluations_checked': 49,
    'formal_mixed_moment_u_squared_v': str(mixed_moment),
    'separators': separators,
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'writeup_sha256': hashlib.sha256(
        (BASE/'cayley-bacharach-transfer-audit.md').read_bytes()).hexdigest(),
    'scope': 'Exact rational finite replay. The general theorem is a written proof. '
             'No new Lean declarations and no unrestricted exponent improvement.',
    'main_target_proved': False,
}
(BASE/'cayley-bacharach-transfer-audit.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k: result[k] for k in ['status', 'restricted_moment_checks',
      'separator_evaluations_checked', 'formal_mixed_moment_u_squared_v']}))
