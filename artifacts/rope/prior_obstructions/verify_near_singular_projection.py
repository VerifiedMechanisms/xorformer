#!/usr/bin/env python3
"""Check exact pure atoms whose cleared selector projection meets 364 labels.

This is deliberately NOT a Boolean separation: the unprojected score has many
wrong labels. The certificate removes the free-constant relaxation from the
projected quadratic search and supplies an exact denominator seed for lifting.
Verification uses only rational arithmetic from the standard library.
"""

from fractions import Fraction as F
from itertools import product
import argparse
import json
from pathlib import Path


def points():
    base = [-1] * 16
    yield base, -1
    for i in range(16):
        z = base.copy()
        z[i] = 1
        yield z, 1
    for i, j in product(range(8), repeat=2):
        if i != j:
            z = base.copy()
            z[2 * i] = z[2 * j + 1] = 1
            yield z, -1
    for j in range(8):
        plus = {1, 2, 3} if j == 0 else {0, *[k for k in range(1, 8) if k != j][:2]}
        for s, a in product((-1, 1), repeat=2):
            z = base.copy()
            for i in range(8):
                z[2 * i + 1] = a if i == j else s * (1 if i in plus else -1)
            yield z, -a


def verify(rec):
    atoms = rec['atoms']
    assert len(atoms) == 4
    for p in atoms:
        assert F(p['gamma']) > 0
        assert all(F(a) > 0 for a in p['a'])
        assert all(F(b) > 0 for b in p['b'])

    def cleared(z):
        den, num = [], []
        for p in atoms:
            weights = [F(p['b'][i] if z[i] == 1 else p['a'][i]) for i in range(17)]
            den.append(F(p['gamma']) + sum(weights))
            num.append(F(p['eta']) + sum(weights[i] * F(p['v1'] if z[i] == 1 else p['v0'])
                                        for i in range(17)))
        assert all(d > 0 for d in den)
        return sum(num[h] * den[(h+1) % 4] * den[(h+2) % 4] * den[(h+3) % 4]
                   for h in range(4))

    labels = {}
    projected_margins = []
    for z, label in points():
        p = cleared(z + [1]) - cleared(z + [-1])
        nz = [-v for v in z]
        p += cleared(nz + [1]) - cleared(nz + [-1])
        projected_margins.append(label * p / 4)
        assert label * p > 0
        for flip, t in product((-1, 1), repeat=2):
            x = tuple(flip * v for v in z) + (t,)
            assert x not in labels or labels[x] == t * label
            labels[x] = t * label
    assert len(labels) == 364
    errors = sum(label * cleared(list(z)) <= 0 for z, label in labels.items())
    assert errors > 0, 'An actual candidate was found; perform full-cube verification!'
    return {
        'status': 'exact pure atoms and exact projected labels only; NOT a Boolean certificate',
        'prescribed_inputs': len(labels),
        'minimum_projected_margin': str(min(projected_margins)),
        'unprojected_prescribed_label_errors': errors,
    }


def rationalize(source):
    epsilon = F(str(source['eps']))
    if source.get('family') == 'balanced_selector':
        k = [F(1), F(1), F(-1), F(1)]
        b = [F(1), F(1), F(0), -F(2) + epsilon]
        st = [F(2), F(2), F(1), F(3)]
        a3 = (-epsilon**2 - 1 + epsilon) / (3 - epsilon)
        a = [(1 - a3) / 2, (1 - a3) / 2, F(-1), a3]
        ell = [(a[h] - k[h] * st[h]) / b[h] if b[h] else F(0) for h in range(4)]
    else:
        k = [F(-1), F(-1), F(1), F(1)]
        b = [F(1), F(1), F(2), -F(4, 5) + epsilon]
        st = [F(2), F(2), F(3), F(2)]
        a = [F(1), F(2), F(-2), F(-1)]
        ell = [(a[h] - k[h] * st[h]) / b[h] for h in range(4)]
    W = [[F(round(v * 10**12), 10**12) for v in row] for row in source['W']]
    S = [row[:4] for row in W] + [st]
    B = [row[4:] for row in W] + [b]
    assert all(S[i][h] > abs(B[i][h]) for i in range(17) for h in range(4))
    maximum = max(sum(row[h] for row in S) for h in range(4))
    alpha = F(1, maximum.numerator // maximum.denominator + 1)
    S = [[alpha * v for v in row] for row in S]
    B = [[alpha * v for v in row] for row in B]
    atoms = []
    for h in range(4):
        v0, v1 = ell[h] - k[h], ell[h] + k[h]
        pa = [S[i][h] - B[i][h] for i in range(17)]
        pb = [S[i][h] + B[i][h] for i in range(17)]
        gamma = 1 - sum(S[i][h] for i in range(17))
        eta = -sum(ell[h] * S[i][h] + k[h] * B[i][h] for i in range(17))
        atoms.append({'gamma': str(gamma), 'eta': str(eta), 'v0': str(v0), 'v1': str(v1),
                      'a': list(map(str, pa)), 'b': list(map(str, pb))})
    return {'status': 'projected selector certificate only; unprojected labels fail',
            'n': 17, 'heads': 4, 'selector_index': 16, 'bias': '0',
            'alpha': str(alpha), 'epsilon': str(epsilon),
            'centered_mass': [[str(v) for v in row] for row in S],
            'centered_bias': [[str(v) for v in row] for row in B],
            'k': list(map(str, k)), 'ell': list(map(str, ell)), 'atoms': atoms}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('file', type=Path)
    parser.add_argument('--rationalize', action='store_true')
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    rec = json.loads(args.file.read_text())
    if args.rationalize:
        rec = rationalize(rec)
    result = verify(rec)
    if args.rationalize:
        assert args.out
        rec['verification'] = result
        args.out.write_text(json.dumps(rec, indent=2) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
