#!/usr/bin/env python3
"""Rational witnesses for a finite tuned Cauchy direction alphabet.

This is a finite test only. It does not establish a scalable alphabet,
balanced assignment inventory, or a superconstant head saving.
Run larger enumerations with heavy.
"""
import argparse
from fractions import Fraction as Q
from itertools import product
import importlib.util
import json
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    'planes', Path(__file__).with_name('reverse-joint-affine-plane-search.py'))
planes = importlib.util.module_from_spec(spec)
spec.loader.exec_module(planes)


def run(groups, power, output):
    eps = Q(1, 10000)
    delta = eps ** power
    kernel = [[1 / (1 - eps * (i + g + 2)) ** 2 for g in range(groups)]
              for i in range(groups)]
    codes = [(sign, k) for sign in (-1, 1) for k in (-1, 0, 1)]
    directions = [(Q(1), sign * (1 + delta * k)) for sign, k in codes]
    covered = {}
    simple = True
    tried = 0
    for labels in product(range(len(codes)), repeat=groups):
        matrix = [[kernel[i][g] * directions[labels[g]][bit] for g in range(groups)]
                  for bit in range(2) for i in range(groups)]
        found, exact = planes.orthants(matrix, [Q(0)] * (2 * groups))
        simple &= exact
        tried += 1
        for pattern, coefficients in found.items():
            if pattern not in covered:
                values = [sum(x * y for x, y in zip(row, coefficients)) for row in matrix]
                assert all(values)
                assert pattern == sum((x > 0) << i for i, x in enumerate(values))
                covered[pattern] = {
                    'labels': list(labels),
                    'coefficients': [[x.numerator, x.denominator] for x in coefficients],
                    'scores': [[x.numerator, x.denominator] for x in values]}
        if len(covered) == 2 ** (2 * groups):
            break
    result = {
        'groups': groups, 'rows': 2 * groups, 'epsilon': [1, 10000],
        'delta_power': power, 'directions_sign_and_k': codes,
        'covered': len(covered), 'all_patterns': 2 ** (2 * groups),
        'assignments_tried': tried, 'all_arrangements_simple': simple,
        'exact_witnesses_checked': True,
        'coverage_complete': len(covered) == 2 ** (2 * groups),
        'note': 'Degenerate missing patterns are not certified impossible. '
                'The amplitude vector is independently chosen per actual target column; '
                'the two displayed bit coordinates are query row types. '
                'Balanced color inventory and asymptotic universality are unproved.',
        'witnesses': covered}
    if output:
        output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'witnesses'}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--groups', type=int, default=3)
    parser.add_argument('--power', type=int, default=3)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    run(args.groups, args.power, args.out)
