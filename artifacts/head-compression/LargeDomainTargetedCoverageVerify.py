#!/usr/bin/env python3
"""Verify a finite universal weighted tangent bank using exact rational arithmetic.

No solver is used.  Each certificate specifies five independent zero rows of a
six-column branch.  A null vector has no additional zero entries.  Independent
perturbation on those five rows realizes all 32 assignments, with both overall
orientations.  An explicit identity branch supplies parity and its complement.
This is a finite-width certificate, not an asymptotic decoder construction.
"""
import argparse
from fractions import Fraction
import itertools
import json
import math


def rref(rows):
    a = [[Fraction(x) for x in row] for row in rows]
    pivots = []
    for col in range(len(a[0])):
        p = next((p for p in range(len(pivots), len(a)) if a[p][col]), None)
        if p is None:
            continue
        r = len(pivots)
        a[r], a[p] = a[p], a[r]
        value = a[r][col]
        a[r] = [x / value for x in a[r]]
        for j in range(len(a)):
            if j != r:
                value = a[j][col]
                a[j] = [x - value * y for x, y in zip(a[j], a[r])]
        pivots.append(col)
        if len(pivots) == len(a):
            break
    return a, pivots


def matrix(data, permutation):
    k, heads, q = (data[name] for name in ('k', 'heads', 'q'))
    rows = []
    for x in range(2**k):
        bits = [1] + [(x >> i) & 1 for i in range(k)]
        den = [q + x + h + 1 for h in range(heads)]
        scale = math.prod(d*d for d in den)
        diff = [sum(bits[i] * (data['v'][permutation[h]][i] - data['u'][h][i])
                    for i in range(k+1)) for h in range(heads)]
        rows.append([diff[h] * scale // den[h]**2 for h in range(heads)]
                    + [scale // den[h] for h in range(heads)])
    return rows


def verify(data):
    k, heads = data['k'], data['heads']
    n, dim = 2**k, 2*heads
    assert k == 3 and heads == 3
    assert data['q'] > 0
    full = (1 << n) - 1
    parity = sum(1 << x for x in range(n) if x.bit_count() % 2 == 0)
    identity = matrix(data, list(range(heads)))
    identity_values = [sum(row[:heads]) for row in identity]
    assert all(v * (-1)**x.bit_count() > 0 for x, v in enumerate(identity_values))
    covered = {parity, full ^ parity}
    for cert in data['certificates']:
        permutation, zero = cert['permutation'], cert['zero_rows']
        assert sorted(permutation) == list(range(heads))
        assert len(set(zero)) == dim-1 and all(0 <= x < n for x in zero)
        rows = matrix(data, permutation)
        reduced, pivots = rref([rows[x] for x in zero])
        assert len(pivots) == dim-1
        free = next(i for i in range(dim) if i not in pivots)
        vector = [Fraction(0)] * dim
        vector[free] = 1
        for r, p in enumerate(pivots):
            vector[p] = -reduced[r][free]
        values = [sum(a*b for a, b in zip(row, vector)) for row in rows]
        assert {x for x, value in enumerate(values) if value == 0} == set(zero)
        positive = sum(1 << x for x in range(n) if values[x] > 0)
        outside = full ^ sum(1 << x for x in zero)
        assert cert['positive_mask'] in (positive, positive ^ outside)
        for subset in range(1 << len(zero)):
            pattern = positive | sum(1 << zero[i] for i in range(len(zero))
                                     if (subset >> i) & 1)
            covered.update((pattern, full ^ pattern))
    assert len(covered) == 1 << n
    print(f"Verified k={k}, H={heads}, q={data['q']}: all {1 << n} strict sign "
          f"patterns from {len(data['certificates'])} exact ray certificates and parity.")
    print("Fixed compact width H/q; no conclusion for growing k is asserted.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate')
    args = parser.parse_args()
    with open(args.certificate) as f:
        verify(json.load(f))
