#!/usr/bin/env python3
"""Exact finite replays of the recursive priority convex decomposition."""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, permutations, product
from math import gcd
from pathlib import Path
import hashlib
import json
import random

from verify_full_table_critical_points import determinant

BASE = Path(__file__).parent


def dictionary(n, both=False):
    N = 1 << n
    tables = set()
    for order in permutations(range(n)):
        cells = []
        for j, i in enumerate(order):
            cells.append(sum(1 << x for x in range(N)
                             if (x >> i) & 1 and not any((x >> p) & 1 for p in order[:j])))
        cells.append(1)  # The all-zero input.
        for labels in product((0, 1), repeat=n+1):
            mask = 0
            for sign, cell in zip(labels, cells):
                if sign:
                    mask |= cell
            tables.add(mask)
            if both:
                tables.add(sum(((mask >> (x ^ (N-1))) & 1) << x for x in range(N)))
    return tables


def decomposition(n, a, b):
    N = 1 << n
    p = [max(a[i+1]-b[i], F(0)) for i in range(n)]
    m = [max(-a[i+1]-b[i], F(0)) for i in range(n)]
    d = [min(b[i], max(-b[i], a[i+1])) for i in range(n)]
    c = [d[i]/b[i] if b[i] else F(0) for i in range(n)]
    assert sum(p) <= 1-a[0] and sum(m) <= 1+a[0]
    assert all(abs(v) <= 1 for v in c)
    kdist = defaultdict(F)
    full = (1 << N)-1
    kdist[full] += (1+a[0]-sum(m))/2
    kdist[0] += (1-a[0]-sum(p))/2
    active_masks = [sum(1 << x for x in range(N) if (x >> i) & 1) for i in range(n)]
    for i in range(n):
        # +literal is 1-2x_i, and -literal is 2x_i-1.
        kdist[full ^ active_masks[i]] += m[i]/2
        kdist[active_masks[i]] += p[i]/2
    assert min(kdist.values()) >= 0 and sum(kdist.values()) == 1

    @lru_cache(None)
    def rec(S):
        W = 1+sum(b[i] for i in range(n) if (S >> i) & 1)
        out = defaultdict(F)
        for mask, weight in kdist.items():
            out[mask] += weight/W
        for i in range(n):
            if not (S >> i) & 1 or not b[i]:
                continue
            for mask, weight in rec(S ^ (1 << i)).items():
                minus = mask & (full ^ active_masks[i])
                plus = minus | active_masks[i]
                out[plus] += b[i]*weight*(1+c[i])/(2*W)
                out[minus] += b[i]*weight*(1-c[i])/(2*W)
        return {mask: weight for mask, weight in out.items() if weight}

    result = rec((1 << n)-1)
    assert all(isinstance(weight, F) and weight > 0 for weight in result.values())
    assert sum(result.values()) == 1
    for x in range(N):
        num = a[0]+sum(a[i+1] for i in range(n) if (x >> i) & 1)
        den = 1+sum(b[i] for i in range(n) if (x >> i) & 1)
        actual = sum(weight*(2*((mask >> x) & 1)-1) for mask, weight in result.items())
        assert actual == num/den and abs(actual) <= 1
    return result


rng = random.Random(7485202)
cases = []
for n in range(1, 6):
    positive = dictionary(n)
    all_tables = dictionary(n, both=True)
    for trial in range(12):
        b = [F(rng.randrange(0, 9), rng.randrange(1, 6)) for _ in range(n)]
        # Build an amplitude-one affine k as a convex combination of signed literals.
        weights = [F(rng.randrange(1, 11)) for _ in range(2*(n+1))]
        total = sum(weights)
        weights = [w/total for w in weights]
        k = [F(0)]*(n+1)
        for i in range(n+1):
            signed = weights[2*i]-weights[2*i+1]
            k[0] += signed
            if i:
                k[i] -= 2*signed
        c = [F(rng.randrange(-5, 6), 5) for _ in range(n)]
        a = [k[0]]+[k[i+1]+b[i]*c[i] for i in range(n)]
        result = decomposition(n, a, b)
        assert set(result) <= positive
        cases.append({'n': n, 'trial': trial, 'convex_support': len(result),
                      'positive_dictionary_size': len(positive),
                      'combined_dictionary_size': len(all_tables)})
    parity = [(-1)**x.bit_count() for x in range(1 << n)]
    assert max(abs(sum(parity[x]*(2*((mask >> x) & 1)-1) for x in range(1 << n)))
               for mask in all_tables) == 2

# Exact two-bit certificate for maximal convex support of one head.
N = 4
D = sorted(tuple(2*((mask >> x) & 1)-1 for x in range(N))
           for mask in dictionary(2, both=True))
assert len(D) == 14
planes = set()
for indices in combinations(range(len(D)), N):
    M = [[F(1)]+list(map(F, D[i])) for i in indices]
    row = [(-1)**j*determinant([[v for k, v in enumerate(r) if k != j] for r in M])
           for j in range(N+1)]
    assert all(v.denominator == 1 for v in row)
    row = [int(v) for v in row]
    if not any(row):
        continue
    factor = 0
    for v in row:
        factor = gcd(factor, v)
    row = tuple(v//factor for v in row)
    if next(v for v in row if v) < 0:
        row = tuple(-v for v in row)
    assert all(row[0]+sum(a*b for a, b in zip(row[1:], D[i])) == 0 for i in indices)
    planes.add(row)
planes = sorted(planes)
assert len(planes) == 97
cover = []
for indices in combinations(range(len(D)), N):
    j = next(j for j, row in enumerate(planes)
             if all(row[0]+sum(a*b for a, b in zip(row[1:], D[i])) == 0 for i in indices))
    cover.append({'indices': indices, 'plane': j})
table = [F(1, 2*(1+s)) for s in range(N)]
evaluations = [F(row[0])+sum(a*b for a, b in zip(row[1:], table)) for row in planes]
assert all(evaluations) and min(map(abs, evaluations)) == F(1, 24)
small_certificate = {'dictionary': D, 'planes': planes, 'four_point_cover': cover,
                     'table': list(map(str, table)), 'plane_evaluations': list(map(str, evaluations)),
                     'status': 'PASS', 'scope': 'Exact real-table convex support, not Boolean head complexity.'}
(BASE/'priority-convex-two-bit-certificate.json').write_text(json.dumps(small_certificate, indent=2)+'\n')
report = {'status': 'PASS', 'decomposition_cases': len(cases), 'cases': cases,
          'two_bit_planes': len(planes), 'four_point_sets_covered': len(cover),
          'minimum_absolute_plane_evaluation': '1/24',
          'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'scope': 'Finite exact checks; general convex-hull and maximal-support theorems are written separately.',
          'main_target_proved': False}
(BASE/'priority-convex-rational-audit.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({k: v for k, v in report.items() if k != 'cases'}, indent=2))
