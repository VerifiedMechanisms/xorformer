#!/usr/bin/env python3
"""Search genuinely variable affine permutation lists and ideal first variations.

The first list is an explicit weighted interval completion. The second is
an arbitrary integer affine map of the Boolean cube into permutations of
the same arithmetic root list. Numerator perturbations are rational affine
forms. A returned witness is checked with independent Fraction arithmetic
on every vertex and at every root. UNSAT concerns only this specified
ansatz; timeout is not an impossibility result. Run through heavy.
"""
import argparse
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import time

import z3


def weighted_completion(weights):
    n = len(weights)
    rows = [[0] + list(weights)]
    prefix = 0
    for i, weight in enumerate(weights):
        for j in range(weight):
            row = [j + prefix + 1] + [0] * n
            row[i + 1] = -prefix - 1
            for k in range(i + 1, n):
                row[k + 1] = weights[k]
            rows.append(row)
        prefix += weight
    return rows


def affine(row, bits):
    return row[0] + sum(a * b for a, b in zip(row[1:], bits))


def verify(record):
    u = record['u']
    v = record['v']
    a = [[Fraction(t) for t in row] for row in record['a']]
    b = [[Fraction(t) for t in row] for row in record['b']]
    n, m = record['n'], len(u)
    assert all(len(row) == n + 1 for rows in (u, v, a, b) for row in rows)
    assert all(len(rows) == m for rows in (v, a, b))
    residues = [(-1)**j * math.factorial(j) * math.factorial(m-1-j)
                for j in range(m)]
    minimum = None
    for bits in itertools.product((0, 1), repeat=n):
        ur = [affine(row, bits) for row in u]
        vr = [affine(row, bits) for row in v]
        assert sorted(ur) == sorted(vr) == list(range(m))
        outputs = [residues[j] * (affine(a[ur.index(j)], bits)
                                  - affine(b[vr.index(j)], bits))
                   for j in range(m)]
        assert len(set(outputs)) == 1
        margin = (-1)**sum(bits) * outputs[0]
        assert margin >= 1
        minimum = margin if minimum is None else min(minimum, margin)
    return {'all_vertices_checked': 1 << n,
            'all_root_values_checked': m * (1 << n),
            'minimum_parity_margin': str(minimum),
            'arithmetic': 'Python arbitrary-precision integers and Fraction',
            'scope': 'One ideal first variation, not the universal head bound.'}


def rational(model, expr):
    value = model.eval(expr, model_completion=True)
    assert z3.is_rational_value(value), value
    return str(Fraction(value.numerator_as_long(), value.denominator_as_long()))


def solve(weights, seconds, seed):
    started = time.monotonic()
    n, m = len(weights), 1 + sum(weights)
    u = weighted_completion(weights)
    # Row permutation at zero fixes these constants without loss in this ansatz.
    v = [[j] + [z3.Int(f'v_{j}_{i}') for i in range(n)] for j in range(m)]
    a = [[z3.Real(f'a_{j}_{i}') for i in range(n+1)] for j in range(m)]
    b = [[z3.Real(f'b_{j}_{i}') for i in range(n+1)] for j in range(m)]
    solver = z3.Solver()
    solver.set(timeout=int(seconds * 1000), random_seed=seed)
    for row in v:
        for entry in row[1:]:
            solver.add(entry >= 1-m, entry <= m-1)
    for i in range(1, n+1):
        solver.add(z3.Sum([row[i] for row in v]) == 0)
    residues = [(-1)**j * math.factorial(j) * math.factorial(m-1-j)
                for j in range(m)]
    for index, bits in enumerate(itertools.product((0, 1), repeat=n)):
        ur = [affine(row, bits) for row in u]
        assert sorted(ur) == list(range(m))
        vr = [affine(row, bits) for row in v]
        solver.add(z3.Distinct(vr))
        solver.add(*[z3.And(t >= 0, t < m) for t in vr])
        r = z3.Real(f'r_{index}')
        solver.add((-1)**sum(bits) * r >= 1)
        for j in range(m):
            av = affine(a[ur.index(j)], bits)
            bv = z3.Sum([z3.If(vr[h] == j, affine(b[h], bits), 0)
                         for h in range(m)])
            solver.add(residues[j] * (av - bv) == r)
    result = solver.check()
    record = {'n': n, 'weights': weights, 'roots': m,
              'status': str(result), 'seconds': time.monotonic()-started,
              'seed': seed,
              'scope': 'Fixed weighted first list; variable integer affine second list; parity signs for the ideal first variation.',
              'target_proved': False}
    if result == z3.sat:
        model = solver.model()
        record.update(u=u,
                      v=[[row[0]] + [model.eval(t).as_long() for t in row[1:]]
                         for row in v],
                      a=[[rational(model, t) for t in row] for row in a],
                      b=[[rational(model, t) for t in row] for row in b])
        record['audit'] = verify(record)
    elif result == z3.unknown:
        record['reason_unknown'] = solver.reason_unknown()
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--weights', type=int, nargs='+', required=True)
    parser.add_argument('--seconds', type=float, default=3600)
    parser.add_argument('--seed', type=int, default=2026112313)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--verify', type=Path)
    args = parser.parse_args()
    assert args.weights and min(args.weights) > 0
    if args.verify:
        record = verify(json.loads(args.verify.read_text()))
    else:
        record = solve(args.weights, args.seconds, args.seed)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({k:v for k,v in record.items() if k not in ('u','v','a','b')}), flush=True)


if __name__ == '__main__':
    main()
