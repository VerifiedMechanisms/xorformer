"""Improve normalized denominator size of a pure-three cubic relaxation.

This optimizes coefficients only.  It makes no Boolean separation claim.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog, minimize
import torch

torch.set_num_threads(1)
torch.set_default_dtype(torch.float64)
PAIRS = list(itertools.product(range(6, 8), range(8, 11)))
WEIGHTS = []
for i in range(6):
    for j in range(6):
        if i != j:
            w = np.zeros((6, 6)); w[i, j] = 1; WEIGHTS.append(w)
for j in range(6):
    w = np.zeros((6, 6)); w[:, j] = -1; WEIGHTS.append(w)


def coefficients(b, k):
    a = np.zeros((6, 6, 34))
    for i in range(6):
        for col, pair in enumerate(PAIRS):
            axes = [i] + list(pair)
            for h in range(3):
                p, q = [v for v in range(3) if v != h]
                for v in axes:
                    w, u = [v2 for v2 in axes if v2 != v]
                    a[i, col, h * 11 + v] = k[h] * (b[p, w] * b[q, u] + b[q, w] * b[p, u])
            a[i, col, -1] = sum(np.prod([b[h, axes[perm[h]]] for h in range(3)])
                               for perm in itertools.permutations(range(3)))
    return a


def derivative(b, s, k, lam, weights):
    bt = torch.tensor(b, requires_grad=True)
    total = torch.tensor(0.)
    for i in range(6):
        for col, pair in enumerate(PAIRS):
            axes = [i] + list(pair)
            value = torch.tensor(0.)
            for h in range(3):
                p, q = [v for v in range(3) if v != h]
                for v in axes:
                    w, u = [v2 for v2 in axes if v2 != v]
                    value = value + k[h] * s[h, v] * (bt[p, w] * bt[q, u] + bt[q, w] * bt[p, u])
            for perm in itertools.permutations(range(3)):
                value = value + lam * bt[0, axes[perm[0]]] * bt[1, axes[perm[1]]] * bt[2, axes[perm[2]]]
            total = total + weights[i, col] * value
    total.backward()
    return bt.grad.numpy()


def solve(b, k, delta=1e-5):
    a = coefficients(b, k)
    matrix = np.zeros((39, 37))
    for i, w in enumerate(WEIGHTS):
        matrix[i, :34] = np.einsum('ij,ijv->v', w, a)
    for h in range(3):
        matrix[36 + h, h * 11:(h + 1) * 11] = 1
        matrix[36 + h, 34] = -1
    rhs = np.r_[np.full(36, -delta), np.zeros(3)]
    objective = np.zeros(37); objective[34] = 1; objective[35:] = 1e-5
    eq = np.zeros((1, 37)); eq[0, 33] = 1; eq[0, 35] = -1; eq[0, 36] = 1
    bounds = [(abs(v) + 1e-5, None) for v in b.ravel()] + [(None, None)] + [(0, None)] * 3
    result = linprog(objective, A_ub=matrix, b_ub=rhs, A_eq=eq, b_eq=[0],
                     bounds=bounds, method='highs', options={'time_limit': 3.})
    if not result.success:
        return None
    s, lam = result.x[:33].reshape(3, 11), result.x[33]
    mu = -result.ineqlin.marginals[:36]
    weights = sum(w * v for w, v in zip(WEIGHTS, mu))
    grad = derivative(b, s, k, lam, weights)
    grad += result.lower.marginals[:33].reshape(3, 11) * np.sign(b)
    scale = 1 / (1 + s.sum(axis=1))
    bn, sn = b * scale[:, None], s * scale[:, None]
    c = np.einsum('ijv,v->ij', coefficients(bn, k), np.r_[sn.ravel(), lam])
    record = {'objective': float(result.fun), 'beta': bn.tolist(), 'mass': sn.tolist(),
              'signs': k.tolist(), 'constant': float(lam), 'C': c.tolist(),
              'beta_l1': abs(bn).sum(axis=1).tolist(),
              'offmax': float(c[~np.eye(6, dtype=bool)].max()),
              'colmin': float(c.sum(axis=0).min()),
              'status': 'numerical coefficient relaxation only'}
    return result.fun, grad, record


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed-file', required=True, type=Path)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--iterations', type=int, default=100)
    ap.add_argument('--seconds', type=int, default=120)
    ap.add_argument('--restarts', type=int, default=4)
    args = ap.parse_args()
    seed = json.loads(args.seed_file.read_text())
    b0 = np.array(seed.get('b', seed.get('beta')))
    b0 /= np.sum(abs(b0), axis=1, keepdims=True)
    k = np.array(seed.get('k', seed.get('signs')))
    rng = np.random.default_rng(271828)
    for restart in range(args.restarts):
        start, best = time.time(), [None]
        bstart = b0 + (rng.normal(size=b0.shape) * .001 if restart else 0)
        def fg(flat):
            if time.time() - start > args.seconds:
                raise TimeoutError
            v = flat.reshape(3, 11)
            norm = np.sum(abs(v), axis=1, keepdims=True)
            b = v / norm
            result = solve(b, k)
            if result is None:
                return 1e12, np.zeros_like(flat)
            value, grad, record = result
            if best[0] is None or value < best[0]['objective']:
                best[0] = record
                args.out.with_suffix('.checkpoint.json').write_text(json.dumps(record))
                print({'restart': restart, 'objective': value,
                       'beta_l1': record['beta_l1'], 'seconds': time.time() - start}, flush=True)
            gradient = (grad - np.sum(grad * b, axis=1, keepdims=True) * np.sign(v)) / norm
            return value, gradient.ravel()
        try:
            minimize(fg, bstart.ravel(), jac=True, method='L-BFGS-B',
                     options={'maxiter': args.iterations, 'maxls': 20, 'ftol': 1e-12})
        except TimeoutError:
            pass
        if best[0] is not None:
            best[0].update({'restart': restart, 'seconds': time.time() - start})
            with args.out.open('a') as out:
                out.write(json.dumps(best[0]) + '\n')
