"""Pure-four variable projection with hard projected M-matrix constraints.

All output is numerical and uncertified.  In particular an infeasible fixed-beta
LP or an unsuccessful optimization is not an architectural lower bound.
"""
import argparse
import json
from pathlib import Path
import sys
import time

import numpy as np
from scipy.optimize import linprog, minimize
import torch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'four_head_middle'))
from search_fixed_denominator_lp import full_pattern, encode

torch.set_num_threads(1)
torch.set_default_dtype(torch.float64)
Z, Y = full_pattern()
X = np.c_[np.ones(len(Z)), Z]
N, H = 17, 4
NV = H * (N + 1)
ELL, K, BASE = NV, NV + H, NV + 2 * H


def cross_rows(beta):
    """Coefficient of selector*x_i*y_j in the cleared polynomial."""
    rows = np.zeros((8, 8, H, N + 1))
    for h in range(H):
        other = [k for k in range(H) if k != h]
        b = beta[other]
        total = b.sum(axis=0)
        pair = np.outer(total, total) - b.T @ b
        triple = np.zeros((8, 8))
        for k in range(3):
            l, m = [q for q in range(3) if q != k]
            triple += b[k, 0] * (np.outer(b[l, 1:9], b[m, 9:17]) +
                                         np.outer(b[m, 1:9], b[l, 9:17]))
        rows[:, :, h, 0] = triple
        rows[:, :, h, 1] = pair[1:9, 9:17]
        for i in range(8):
            rows[i, :, h, i + 2] = pair[0, 9:17]
        for j in range(8):
            rows[:, j, h, j + 10] = pair[1:9, 0]
    return rows.reshape(8, 8, NV)


def cross_derivative(beta, numerators, weights):
    b = torch.tensor(beta, requires_grad=True)
    a = torch.tensor(numerators)
    cross = torch.zeros((8, 8))
    for h in range(H):
        other = [k for k in range(H) if k != h]
        bh = b[other]
        total = bh.sum(dim=0)
        pair = torch.outer(total, total) - bh.T @ bh
        triple = torch.zeros((8, 8))
        for k in range(3):
            l, m = [q for q in range(3) if q != k]
            triple = triple + bh[k, 0] * (torch.outer(bh[l, 1:9], bh[m, 9:17]) +
                                                 torch.outer(bh[m, 1:9], bh[l, 9:17]))
        cross = cross + a[h, 0] * triple + a[h, 1] * pair[1:9, 9:17] + \
            torch.outer(a[h, 2:10], pair[0, 9:17]) + \
            torch.outer(pair[1:9, 0], a[h, 10:18])
    objective = torch.sum(cross * torch.tensor(weights))
    objective.backward()
    return b.grad.detach().numpy()


def solve(beta, signs, delta=1e-7, regularizer=1e-8, cross_sign=1,
          positive_weight=1, hard_positive=False):
    d = 1 + Z @ beta.T
    if d.min() <= 0:
        return None
    count = len(Y)
    width = BASE + count + 2 * NV
    rows, rhs = [], []
    for j in range(count):
        row = np.zeros(width)
        for h in range(H):
            row[h * (N + 1):(h + 1) * (N + 1)] = -Y[j] * X[j] / d[j, h]
        row[BASE + j] = -1
        rows.append(row)
        rhs.append(-1)
    for h in range(H):
        for i in range(N):
            row = np.zeros(width)
            row[h * (N + 1) + i + 1] = -signs[h]
            row[ELL + h] = beta[h, i]
            row[K + h] = abs(beta[h, i])
            rows.append(row)
            rhs.append(-1e-7)
        row = np.zeros(width)
        row[h * (N + 1) + 1:(h + 1) * (N + 1)] = signs[h]
        row[ELL + h] = -sum(beta[h])
        row[K + h] = -1
        rows.append(row)
        rhs.append(-1e-7)
    projected = cross_sign * cross_rows(beta)
    cross_offset = len(rows)
    cross_locations = []
    # Row normalization prevents HiGHS treating tiny beta-polynomial entries as
    # structural zeros.  The same scale is included in the envelope derivative.
    scales = []
    for i in range(8):
        for j in range(8):
            if i == j:
                continue
            scale = max(np.max(np.abs(projected[i, j])), 1e-15)
            row = np.zeros(width)
            row[:NV] = projected[i, j] / scale
            rows.append(row)
            rhs.append(-delta / scale)
            cross_locations.append((i, j))
            scales.append(scale)
    for j in range(8):
        values = -projected[:, j].sum(axis=0)
        scale = max(np.max(np.abs(values)), 1e-15)
        row = np.zeros(width)
        row[:NV] = values / scale
        rows.append(row)
        rhs.append(-delta / scale)
        scales.append(scale)
    objective = np.zeros(width)
    spatial_positive = Y * Z[:, 0] > 0
    label_weights = np.where(spatial_positive, positive_weight, 1.)
    objective[BASE:BASE + count] = label_weights / label_weights.sum()
    objective[BASE + count:] = regularizer
    equality = np.zeros((NV, width))
    for i in range(NV):
        equality[i, i] = 1
        equality[i, BASE + count + i] = -1
        equality[i, BASE + count + NV + i] = 1
    bounds = [(None, None)] * (NV + H) + [(1e-7, None)] * H + [(0, None)] * (count + 2 * NV)
    if hard_positive:
        for i in np.flatnonzero(spatial_positive):
            bounds[BASE + i] = (0, 0)
    lp = linprog(objective, A_ub=np.array(rows), b_ub=np.array(rhs),
                 A_eq=equality, b_eq=np.zeros(NV), bounds=bounds, method='highs',
                 options={'time_limit': 5.0})
    if not lp.success:
        return {'success': False, 'message': lp.message}
    theta = lp.x
    numerators = theta[:NV].reshape(H, N + 1)
    num = X @ numerators.T
    score = np.sum(num / d, axis=1)
    margin = Y * score
    cross = np.einsum('ijv,v->ij', projected, theta[:NV])
    mu = -lp.ineqlin.marginals
    grad = np.zeros_like(beta)
    for h in range(H):
        grad[h] = np.sum((mu[:count] * Y * num[:, h] / d[:, h] ** 2)[:, None] * Z, axis=0)
        offset = count + h * (N + 1)
        grad[h] += mu[offset:offset + N] * (theta[ELL + h] + theta[K + h] * np.sign(beta[h]))
        grad[h] -= mu[offset + N] * theta[ELL + h]
    weights = np.zeros((8, 8))
    for k, (i, j) in enumerate(cross_locations):
        weights[i, j] = mu[cross_offset + k] / scales[k]
    for j in range(8):
        weights[:, j] -= mu[cross_offset + 56 + j] / scales[56 + j]
    grad += cross_sign * cross_derivative(beta, numerators, weights)
    return {'success': True, 'loss': float(lp.fun), 'errors': int(sum(margin <= 0)),
            'minimum_margin': float(min(margin)), 'beta': beta.tolist(), 'signs': signs.tolist(),
            'numerators': numerators.tolist(), 'ell_signed': theta[ELL:K].tolist(),
            'k_absolute': theta[K:BASE].tolist(), 'cross': cross.tolist(), 'gradient': grad,
            'off_diagonal_max': float(np.max(cross[~np.eye(8, dtype=bool)])),
            'column_sum_min': float(np.min(cross.sum(axis=0)))}


def main():
    global Z, Y, X
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed-file', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--restarts', type=int, default=16)
    parser.add_argument('--iterations', type=int, default=100)
    parser.add_argument('--delta', type=float, default=1e-7)
    parser.add_argument('--regularizer', type=float, default=1e-8)
    parser.add_argument('--seed', type=int, default=294897)
    parser.add_argument('--cross-sign', type=int, choices=[-1, 1], default=1)
    parser.add_argument('--flip-right', action='store_true')
    parser.add_argument('--old-pattern', action='store_true')
    parser.add_argument('--seconds-per-restart', type=float, default=120)
    parser.add_argument('--start-mask', type=int, default=0)
    parser.add_argument('--positive-weight', type=float, default=1.)
    parser.add_argument('--hard-positive', action='store_true')
    args = parser.parse_args()
    if args.old_pattern:
        base = -np.ones(16)
        points = [(base.copy(), -1)]
        for i in range(16):
            z = base.copy()
            z[i] = 1
            points.append((z, 1))
        for i in range(8):
            for j in range(8):
                if i != j:
                    z = base.copy()
                    z[i] = z[8 + j] = 1
                    points.append((z, -1))
        for j in range(8):
            for k in range(j):
                z = base.copy()
                z[8 + j] = z[8 + k] = 1
                points.append((z, -1))
        inputs = {}
        for z, y in points:
            for flip in [-1, 1]:
                for t in [-1, 1]:
                    inputs[tuple([t] + list(flip * z))] = t * y
        Z, Y = np.array(list(inputs)), np.array(list(inputs.values()))
    if args.flip_right:
        Z = Z.copy()
        Z[:, 9:17] *= -1
    X = np.c_[np.ones(len(Z)), Z]
    obj = json.loads(args.seed_file.read_text())
    beta0 = np.array(obj['beta'])
    rng = np.random.default_rng(args.seed)
    for restart in range(args.restarts):
        sign_mask = (restart + args.start_mask) % 16
        signs = np.array([-1 if sign_mask >> h & 1 else 1 for h in range(H)])
        beta = beta0.copy()
        if restart >= 16:
            beta += rng.normal(0, .001, beta.shape)
        beta *= min(1, .95 / np.max(np.sum(abs(beta), axis=1)))
        v = beta / (1 - np.sum(abs(beta), axis=1, keepdims=True))
        best, calls = [None], [0]
        start = time.time()

        def fg(flat):
            if time.time() - start > args.seconds_per_restart:
                raise TimeoutError('bounded restart time exhausted')
            v = flat.reshape(H, N)
            beta, den = encode(v)
            fit = solve(beta, signs, args.delta, args.regularizer, args.cross_sign,
                        args.positive_weight, args.hard_positive)
            calls[0] += 1
            if not fit or not fit['success']:
                return 1e10, np.zeros_like(flat)
            grad = fit.pop('gradient')
            if best[0] is None or fit['loss'] < best[0]['loss']:
                best[0] = fit
                args.out.with_suffix('.checkpoint.json').write_text(json.dumps({**fit,
                    'restart': restart, 'sign_mask': sign_mask,
                    'status': 'numerical intermediate hard-cross proposal only'}))
            transformed = (grad - np.sum(grad * v, axis=1, keepdims=True) *
                           v / np.sqrt(v * v + 1e-16) / den) / den
            return fit['loss'], transformed.ravel()

        try:
            result = minimize(fg, v.ravel(), jac=True, method='L-BFGS-B',
                              options={'maxiter': args.iterations, 'ftol': 1e-14,
                                       'gtol': 1e-8, 'maxls': 30})
            optimizer_message = str(result.message)
        except TimeoutError as error:
            optimizer_message = str(error)
        fit = best[0]
        if fit is None:
            print({'restart': restart, 'status': 'no feasible hard-cross LP'}, flush=True)
            continue
        fit.update(restart=restart, seconds=time.time() - start, calls=calls[0],
                   status='numerical hard-cross proposal only', optimizer_message=optimizer_message,
                   flip_right=args.flip_right, old_pattern=args.old_pattern,
                   cross_sign=args.cross_sign, sign_mask=sign_mask,
                   positive_weight=args.positive_weight, hard_positive=args.hard_positive)
        with args.out.open('a') as output:
            output.write(json.dumps(fit) + '\n')
        print({key: fit[key] for key in ['restart', 'loss', 'errors', 'minimum_margin',
                                        'off_diagonal_max', 'column_sum_min', 'seconds']}, flush=True)
        if fit['minimum_margin'] > 0 and fit['off_diagonal_max'] < 0 and fit['column_sum_min'] > 0:
            print('FULL NUMERICAL PATTERN FOUND; EXACT CERTIFICATION STILL REQUIRED', flush=True)
            return


if __name__ == '__main__':
    main()
