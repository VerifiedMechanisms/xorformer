#!/usr/bin/env python3
"""Verify the four-bit nonparity three-head certificate using exact integers.

No numerical solver, symbolic algebra package, or external certificate checker
is trusted. A rank-13 cleared-denominator feature matrix has a three-dimensional
left kernel. Each listed four-row circuit gives a vector in its column space
with a prescribed sign on those four coordinates. Because its other coordinates
are zero, a small perturbation inside that column space realizes every strict
sign assignment extending the four circuit signs. See Theorem 020 for the
linear algebra and perturbation proof. The final check exhausts all 2^16 labels.
"""
import itertools
import json
import math
from pathlib import Path


def determinant(matrix):
    """Fraction-free Bareiss determinant, with exact-division assertions."""
    a = [list(row) for row in matrix]
    n = len(a)
    assert all(len(row) == n for row in a)
    previous, sign = 1, 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def feature_matrix(slopes):
    assert len(slopes) == 3 and all(len(row) == 4 for row in slopes)
    assert all(isinstance(c, int) and c > 0 for row in slopes for c in row)
    result = []
    for x in itertools.product((0, 1), repeat=4):
        d = [1 + sum(c * bit for c, bit in zip(row, x)) for row in slopes]
        product = math.prod(d)
        result.append([product] + [x[i] * (product // d[h])
                                   for h in range(3) for i in range(4)])
    return result


def verify(path):
    data = json.loads(path.read_text())
    vertices = list(itertools.product((0, 1), repeat=4))
    assert data['vertex_order'] == [list(x) for x in vertices]
    families = data['families']
    for family in families:
        t = feature_matrix(family['slopes'])
        k = family['kernel']
        assert len(k) == 16 and all(len(row) == 3 for row in k)
        assert all(isinstance(a, int) for row in k for a in row)
        assert all(sum(k[i][a] * t[i][b] for i in range(16)) == 0
                   for a in range(3) for b in range(13))
        rows = family['rank_rows']
        assert len(rows) == 13 and len(set(rows)) == 13
        assert all(0 <= i < 16 for i in rows)
        assert determinant([t[i] for i in rows]) != 0
        assert any(determinant([k[i] for i in rows]) != 0
                   for rows in itertools.combinations(range(16), 3))

    patterns = []
    for family_index, indices in data['circuits']:
        assert 0 <= family_index < len(families)
        assert len(indices) == 4 and len(set(indices)) == 4
        assert all(0 <= i < 16 for i in indices)
        k = families[family_index]['kernel']
        coefficients = [(-1)**j * determinant([k[indices[l]] for l in range(4)
                                               if l != j]) for j in range(4)]
        assert all(a != 0 for a in coefficients)
        assert all(sum(coefficients[j] * k[indices[j]][a] for j in range(4)) == 0
                   for a in range(3))
        support = sum(1 << i for i in indices)
        positive = sum(1 << i for i, c in zip(indices, coefficients) if c > 0)
        patterns.append((support, positive))

    uncovered = [label for label in range(1 << 16)
                 if not any(label & support in (positive, support ^ positive)
                            for support, positive in patterns)]
    parity = sum((sum(x) % 2) << i for i, x in enumerate(vertices))
    assert uncovered == sorted((parity, ((1 << 16) - 1) ^ parity))
    assert data['uncovered'] == uncovered
    templates_path = path.with_name('four_bit_three_head_templates.json')
    templates = json.loads(templates_path.read_text())
    assert len(templates) == len(patterns)
    for ci, template in enumerate(templates):
        fi, indices = data['circuits'][ci]
        support, positive = patterns[ci]
        assert template['family'] == fi and template['support'] == indices
        assert template['positive'] in (positive, support ^ positive)
        free = [i for i in range(16) if i not in indices]
        assert template['free'] == free
        t = feature_matrix(families[fi]['slopes'])
        base, adjust, scale = template['base'], template['adjust'], template['scale']
        assert len(base) == 13 and len(adjust) == 12
        assert all(len(row) == 13 for row in adjust) and scale > 0
        evaluate = lambda a, v: sum(t[v][k] * a[k] for k in range(13))
        for v in range(16):
            b = evaluate(base, v)
            u = [evaluate(row, v) for row in adjust]
            if v in free:
                assert b == 0
                assert all(value == (scale if free[j] == v else 0)
                           for j, value in enumerate(u))
            else:
                assert abs(b) > sum(abs(value) for value in u)
                assert (b > 0) == bool(template['positive'] & (1 << v))

    print(f'PASS: {len(families)} integer feature matrices, '

          f'{len(patterns)} full-support circuits and strict templates, '
          '65534 nonparity labels covered.')
    print(f'Only uncovered labels: {uncovered} (parity and its complement).')
    return data, patterns


if __name__ == '__main__':
    verify(Path(__file__).with_name('four_bit_three_head_circuits.json'))
