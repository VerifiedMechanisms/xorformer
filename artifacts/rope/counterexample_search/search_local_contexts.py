"""Relaxed independent context offsets for tripartite parity faces.

Free intercepts are not automatically realizable by shared pure auxiliary bits.
The optional one-hot test implements a necessary and sufficient bridge for that
particular encoding, but floating success still needs exact certification.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog, minimize

Z = np.array(list(itertools.product([-1, 1], repeat=3)))
PARITY = np.prod(Z, axis=1)


def cubic(b, u, constant):
    total = constant * sum(np.prod([b[h, p[h]] for h in range(3)])
                           for p in itertools.permutations(range(3)))
    for h in range(3):
        p, q = [v for v in range(3) if v != h]
        for i in range(3):
            j, k = [v for v in range(3) if v != i]
            total += u[h, i] * (b[p, j] * b[q, k] + b[p, k] * b[q, j])
    return total


def fit_constants(b, u, constant, d, desired_sign):
    den = d + Z @ b.T
    if den.min() <= 0:
        return None
    nlin = Z @ u.T
    products = np.column_stack([den[:, (h + 1) % 3] * den[:, (h + 2) % 3]
                                for h in range(3)])
    base = constant * np.prod(den, axis=1) + np.sum(nlin * products, axis=1)
    q, r = np.linalg.qr(products)
    residual = base - q @ (q.T @ base)
    scale = desired_sign * cubic(b, u, constant)
    if scale <= 0:
        return None
    target = desired_sign * PARITY
    a = np.c_[-target[:, None] * q, np.ones(8)]
    result = linprog([0, 0, 0, -1], A_ub=a, b_ub=target * residual / scale,
                     bounds=[(None, None)] * 4, method='highs')
    if not result.success:
        return None
    c = np.linalg.solve(r, scale * result.x[:3] - q.T @ base)
    actual = constant * np.prod(den, axis=1) + np.sum((nlin + c) * products, axis=1)
    margin = float(np.min(target * actual / scale))
    derivative = np.zeros((8, 3))
    for h in range(3):
        p, qh = [v for v in range(3) if v != h]
        derivative[:, h] = constant * den[:, p] * den[:, qh]
        derivative[:, h] += (nlin[:, p] + c[p]) * den[:, qh]
        derivative[:, h] += (nlin[:, qh] + c[qh]) * den[:, p]
    mu = -result.ineqlin.marginals
    grad = -np.sum((mu * target / scale)[:, None] * derivative, axis=0)
    return {'margin': margin, 'lp_margin': float(result.x[-1]),
            'numerator_intercepts': c.tolist(), 'denominator_intercepts': d.tolist(),
            'cubic_magnitude': float(scale), 'gradient': grad}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed-file', required=True, type=Path)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--iterations', type=int, default=100)
    ap.add_argument('--restarts', type=int, default=3)
    ap.add_argument('--full-mass-bound', action='store_true')
    args = ap.parse_args()
    seed = json.loads(args.seed_file.read_text())
    b = np.array(seed.get('beta', seed.get('b')))
    if 'numerators' in seed and 'mass' not in seed and 's' not in seed:
        u = np.array(seed['numerators'])[:, 1:]
        signs = np.array(seed['signs'])
        absolute = np.array(seed['k_absolute'])
        k = signs * absolute
        ell = signs * np.array(seed['ell_signed'])
        s = (u - ell[:, None] * b) / k[:, None]
        constant = 0.
    else:
        s = np.array(seed.get('mass', seed.get('s')))
        k = np.array(seed.get('signs', seed.get('k')))
        u = k[:, None] * s
        constant = seed.get('constant', seed.get('lambda'))
    pairs = list(itertools.product(range(6, 8), range(8, 11)))
    contexts = []
    for i in range(6):
        for col, pair in enumerate(pairs):
            if i != col:
                contexts.append(([[i], [pair[0]], [pair[1]]], -1, ['entry', i, col]))
    for col, pair in enumerate(pairs):
        contexts.append(([list(range(6)), [pair[0]], [pair[1]]], 1, ['column', col]))
    rng = np.random.default_rng(314159)
    for groups, sign, name in contexts:
        bf = np.column_stack([b[:, group].sum(axis=1) for group in groups])
        uf = np.column_stack([u[:, group].sum(axis=1) for group in groups])
        lower = s.sum(axis=1) if args.full_mass_bound else abs(bf).sum(axis=1) + 1e-6
        best = [None]; start = time.time()
        for restart in range(args.restarts):
            def fg(v):
                d = lower + np.exp(v)
                result = fit_constants(bf, uf, constant, d, sign)
                if result is None:
                    return 1e12, np.zeros(3)
                if best[0] is None or result['margin'] > best[0]['margin']:
                    best[0] = {key: value for key, value in result.items() if key != 'gradient'}
                return -result['lp_margin'], result['gradient'] * np.exp(v)
            initial = np.maximum(1 - lower, .05) if restart == 0 else rng.uniform(.01, 2, 3)
            minimize(fg, np.log(initial), jac=True, method='L-BFGS-B',
                     bounds=[(-15, 5)] * 3,
                     options={'maxiter': args.iterations, 'maxls': 20, 'ftol': 1e-12})
        if best[0] is not None:
            record = {'constraint': name, 'groups': groups, 'desired_sign': sign,
                      **best[0], 'seconds': time.time() - start,
                      'status': 'independent context relaxation only; shared pure embedding unproved'}
            with args.out.open('a') as out:
                out.write(json.dumps(record) + '\n')
            print({key: record[key] for key in ['constraint', 'margin', 'seconds']}, flush=True)
