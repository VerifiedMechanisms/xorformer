"""Maximize strict top-degree orientation margins at bounded value scale."""
import argparse
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog, minimize

from improve_multilinear_projection import Problem


def solve(problem, b):
    h, n, hn = problem.h, problem.n, problem.h * problem.n
    K, LAM, DELTA, POS, NEG = hn, hn + h, hn + h + 1, hn + h + 2, hn + h + 3
    width = hn + h + 4
    coefficient_scale = 1e6 if h == 4 else 1.
    coeff = problem.coefficients(b)
    rows, rhs = [], []
    for w in problem.weights:
        a = coefficient_scale * np.einsum('ij,ijv->v', w, coeff)
        row = np.zeros(width); row[:hn] = a[:hn]; row[LAM] = a[-1]; row[DELTA] = 1
        rows.append(row); rhs.append(0.)
    cone_offset = len(rows)
    for g in range(h):
        for i in range(n):
            row = np.zeros(width); row[g * n + i] = -1; row[K + g] = abs(b[g, i])
            rows.append(row); rhs.append(-1e-10)
        row = np.zeros(width); row[g * n:(g + 1) * n] = 1; row[K + g] = -1
        rows.append(row); rhs.append(-1e-10)
    row = np.zeros(width); row[K:K + h] = 1; row[POS:] = 1
    rows.append(row); rhs.append(1.)
    eq = np.zeros((1, width)); eq[0, LAM] = 1; eq[0, POS] = -1; eq[0, NEG] = 1
    objective = np.zeros(width); objective[DELTA] = -1
    bounds = [(0, None)] * width; bounds[LAM] = (None, None)
    result = linprog(objective, A_ub=rows, b_ub=rhs, A_eq=eq, b_eq=[0.],
                     bounds=bounds, method='highs', options={'time_limit': 3.,
                     'dual_feasibility_tolerance': 1e-9, 'primal_feasibility_tolerance': 1e-9})
    if not result.success or result.x[DELTA] <= 0:
        return None
    v = result.x[:hn].reshape(h, n); absolute = result.x[K:K + h]
    lam = result.x[LAM]
    mu = -result.ineqlin.marginals
    weights = sum(w * value * coefficient_scale for w, value in zip(problem.weights, mu))
    grad, _ = problem.derivative(b, v, lam, weights)
    for g in range(h):
        start = cone_offset + g * (n + 1)
        grad[g] += mu[start:start + n] * absolute[g] * np.sign(b[g])
    c = np.einsum('ijv,v->ij', coeff, np.r_[v.ravel(), lam])
    record = {'margin': float(result.x[DELTA] / coefficient_scale), 'beta': b.tolist(),
              'mass': (v / absolute[:, None]).tolist(),
              'k': (problem.k * absolute).tolist(), 'constant': float(lam),
              'C': c.tolist(), 'beta_l1': abs(b).sum(axis=1).tolist(),
              'offmax': float(c[~np.eye(problem.m, dtype=bool)].max()),
              'colmin': float(c.sum(axis=0).min()),
              'status': 'numerical coefficient relaxation only'}
    return result.fun / coefficient_scale, grad / coefficient_scale, record


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed-file', required=True, type=Path)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--restarts', type=int, default=3)
    ap.add_argument('--iterations', type=int, default=200)
    ap.add_argument('--seconds', type=int, default=100)
    args = ap.parse_args()
    seed = json.loads(args.seed_file.read_text())
    b0 = np.array(seed.get('beta', seed.get('b')))
    k0 = np.array(seed.get('k', seed.get('signs')))
    problem = Problem(len(k0), np.sign(k0))
    rng = np.random.default_rng(271831)
    for restart in range(args.restarts):
        start, best, last_print = time.time(), [None], [0.]
        initial = b0 / (1 - abs(b0).sum(axis=1, keepdims=True))
        if restart:
            initial += rng.normal(size=initial.shape) * .002
        def fg(flat):
            if time.time() - start > args.seconds:
                raise TimeoutError
            v = flat.reshape(b0.shape); norm = 1 + abs(v).sum(axis=1, keepdims=True)
            b = v / norm
            result = solve(problem, b)
            if result is None:
                return 1e3, np.zeros_like(flat)
            value, grad, record = result
            if best[0] is None or record['margin'] > best[0]['margin']:
                best[0] = record
                args.out.with_suffix('.checkpoint.json').write_text(json.dumps(record))
                if record['margin'] > last_print[0] * 1.05:
                    last_print[0] = record['margin']
                    print({'restart': restart, 'margin': record['margin'],
                           'beta_l1': record['beta_l1'], 'seconds': time.time() - start}, flush=True)
            gradient = (grad - np.sum(grad * b, axis=1, keepdims=True) * np.sign(v)) / norm
            # Scaling the objective avoids an optimizer stopping at tiny margins.
            return value * 1e6, gradient.ravel() * 1e6
        try:
            minimize(fg, initial.ravel(), jac=True, method='L-BFGS-B',
                     options={'maxiter': args.iterations, 'maxls': 30, 'ftol': 1e-13, 'gtol': 1e-10})
        except TimeoutError:
            pass
        if best[0] is not None:
            best[0].update({'restart': restart, 'seconds': time.time() - start})
            with args.out.open('a') as out:
                out.write(json.dumps(best[0]) + '\n')
