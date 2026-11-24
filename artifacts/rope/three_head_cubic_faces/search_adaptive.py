"""Numerical proposals for a pure-three cubic flattening obstruction.

Thirty negative ordinary parity faces and six positive tied-X parity faces
would force an inverse-positive 6 by 6 cubic flattening.  Backgrounds are
chosen adaptively.  Failed optimization is never a lower bound.
"""
import argparse
import itertools
import json
from pathlib import Path
import sys
import time

import numpy as np
from scipy.optimize import linprog, minimize
import torch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'four_head_middle'))
from search_fixed_denominator_lp import encode

torch.set_num_threads(1)
torch.set_default_dtype(torch.float64)
H, N = 3, 11
NV = H * (N + 1)
ELL, K, BASE = NV, NV + H, NV + 2 * H
MASKS = np.arange(1 << N)
ZALL = 2 * ((MASKS[:, None] >> np.arange(N)) & 1) - 1
XALL = np.c_[np.ones(len(MASKS)), ZALL]
PAIRS = list(itertools.product(range(6, 8), range(8, 11)))
BITS = np.array(list(itertools.product([0, 1], repeat=3)))
PARITY = np.prod(2 * BITS - 1, axis=1)


def face_families():
    families = []
    for i in range(6):
        for j, (y, z) in enumerate(PAIRS):
            if i == j:
                continue
            axes = [1 << i, 1 << y, 1 << z]
            used = sum(axes)
            backgrounds = MASKS[(MASKS & used) == 0]
            faces = backgrounds[:, None] + BITS @ np.array(axes)
            families.append((faces, -PARITY, ('entry', i, j)))
    for j, (y, z) in enumerate(PAIRS):
        axes = [63, 1 << y, 1 << z]
        used = sum(axes)
        backgrounds = MASKS[(MASKS & used) == 0]
        faces = backgrounds[:, None] + BITS @ np.array(axes)
        families.append((faces, PARITY, ('column', j)))
    return families


FAMILIES = face_families()


def choose_faces(score):
    selected, labels, diagnostics = [], [], []
    for faces, desired, name in FAMILIES:
        margins = score[faces] * desired
        # Max-min selection directly seeks a strict parity witness.
        best = int(np.argmax(margins.min(axis=1)))
        selected.extend(faces[best])
        labels.extend(desired)
        diagnostics.append({'constraint': name, 'masks': faces[best].tolist(),
                            'margin': float(margins[best].min())})
    return np.array(selected), np.array(labels), diagnostics


def cross_rows(beta):
    rows = np.zeros((6, 6, H, N + 1))
    for h in range(H):
        p, q = [a for a in range(H) if a != h]
        for i in range(6):
            for j, (y, z) in enumerate(PAIRS):
                rows[i, j, h, i + 1] = beta[p, y] * beta[q, z] + beta[q, y] * beta[p, z]
                rows[i, j, h, y + 1] = beta[p, i] * beta[q, z] + beta[q, i] * beta[p, z]
                rows[i, j, h, z + 1] = beta[p, i] * beta[q, y] + beta[q, i] * beta[p, y]
    return rows.reshape(6, 6, NV)


def cross_derivative(beta, numerators, weights):
    b = torch.tensor(beta, requires_grad=True)
    a = torch.tensor(numerators)
    total = torch.tensor(0.)
    for h in range(H):
        p, q = [v for v in range(H) if v != h]
        for i in range(6):
            for j, (y, z) in enumerate(PAIRS):
                c = a[h, i + 1] * (b[p, y] * b[q, z] + b[q, y] * b[p, z])
                c = c + a[h, y + 1] * (b[p, i] * b[q, z] + b[q, i] * b[p, z])
                c = c + a[h, z + 1] * (b[p, i] * b[q, y] + b[q, i] * b[p, y])
                total = total + weights[i, j] * c
    total.backward()
    return b.grad.numpy()


def solve(beta, signs, selected=None, labels=None, delta=1e-5, regularizer=1e-9):
    count = 0 if selected is None else len(selected)
    width = BASE + count + 2 * NV
    rows, rhs = [], []
    if count:
        z, x = ZALL[selected], XALL[selected]
        den = 1 + z @ beta.T
        for r in range(count):
            row = np.zeros(width)
            row[:NV] = (-labels[r] * x[r][None, :] / den[r, :, None]).ravel()
            row[BASE + r] = -1
            rows.append(row); rhs.append(-1)
    for h in range(H):
        for i in range(N):
            row = np.zeros(width)
            row[h * (N + 1) + i + 1] = -signs[h]
            row[ELL + h] = beta[h, i]
            row[K + h] = abs(beta[h, i])
            rows.append(row); rhs.append(-1e-7)
        row = np.zeros(width)
        row[h * (N + 1) + 1:(h + 1) * (N + 1)] = signs[h]
        row[ELL + h] = -sum(beta[h]); row[K + h] = -1
        rows.append(row); rhs.append(-1e-7)
    cr = cross_rows(beta)
    weights, scales = [], []
    for i in range(6):
        for j in range(6):
            if i == j:
                continue
            w = np.zeros((6, 6)); w[i, j] = 1
            weights.append(w)
    for j in range(6):
        w = np.zeros((6, 6)); w[:, j] = -1
        weights.append(w)
    cross_offset = len(rows)
    for w in weights:
        coeff = np.einsum('ij,ijv->v', w, cr)
        scale = max(np.max(abs(coeff)), 1e-15)
        row = np.zeros(width); row[:NV] = coeff / scale
        rows.append(row); rhs.append(-delta / scale); scales.append(scale)
    objective = np.zeros(width)
    if count: objective[BASE:BASE + count] = 1 / count
    objective[BASE + count:] = regularizer if count else 1.
    equality = np.zeros((NV, width))
    for i in range(NV):
        equality[i, i] = 1
        equality[i, BASE + count + i] = -1
        equality[i, BASE + count + NV + i] = 1
    bounds = [(None, None)] * (NV + H) + [(1e-7, None)] * H
    bounds += [(0, None)] * (count + 2 * NV)
    lp = linprog(objective, A_ub=np.array(rows), b_ub=np.array(rhs),
                 A_eq=equality, b_eq=np.zeros(NV), bounds=bounds,
                 method='highs', options={'time_limit': 3.})
    if not lp.success: return None
    theta = lp.x
    a = theta[:NV].reshape(H, N + 1)
    allscore = np.sum((XALL @ a.T) / (1 + ZALL @ beta.T), axis=1)
    selected_next, labels_next, witnesses = choose_faces(allscore)
    output = {'loss': float(lp.fun), 'beta': beta.tolist(), 'signs': signs.tolist(),
              'numerators': a.tolist(), 'ell_signed': theta[ELL:K].tolist(),
              'k_absolute': theta[K:BASE].tolist(),
              'witness_minimum': min(w['margin'] for w in witnesses),
              'witness_count': sum(w['margin'] > 1e-7 for w in witnesses),
              'witnesses': witnesses, 'status': 'numerical proposal only'}
    if not count: return output
    mu = -lp.ineqlin.marginals
    grad = np.zeros_like(beta)
    num = x @ a.T
    for h in range(H):
        grad[h] = np.sum((mu[:count] * labels * num[:, h] / den[:, h] ** 2)[:, None] * z, axis=0)
        offset = count + h * (N + 1)
        grad[h] += mu[offset:offset + N] * (theta[ELL + h] + theta[K + h] * np.sign(beta[h]))
        grad[h] -= mu[offset + N] * theta[ELL + h]
    cw = sum(w * mu[cross_offset + i] / scales[i] for i, w in enumerate(weights))
    grad += cross_derivative(beta, a, cw)
    output['gradient'] = grad
    output['selected_next'], output['labels_next'] = selected_next, labels_next
    return output


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--seed', type=int, default=41837)
    ap.add_argument('--attempts', type=int, default=1000)
    ap.add_argument('--rounds', type=int, default=10)
    ap.add_argument('--iterations', type=int, default=80)
    ap.add_argument('--seconds', type=float, default=120)
    ap.add_argument('--seed-file', type=Path)
    args = ap.parse_args(); rng = np.random.default_rng(args.seed)
    found = 0
    for attempt in range(args.attempts):
        if args.seed_file:
            seed = json.loads(args.seed_file.read_text())
            beta = np.array(seed['beta'])
        else:
            beta = rng.normal(size=(H, N))
            beta *= rng.uniform(.3, .95, (H, 1)) / np.sum(abs(beta), axis=1, keepdims=True)
        signs = np.array([-1 if attempt >> h & 1 else 1 for h in range(H)])
        seed = solve(beta, signs)
        if not seed:
            if attempt % 50 == 0: print({'attempt': attempt, 'projected_feasible': found}, flush=True)
            continue
        found += 1; start = time.time(); best = seed
        print({'attempt': attempt, 'projected_feasible': found,
               'witnesses': seed['witness_count']}, flush=True)
        for round_index in range(args.rounds):
            a = np.array(best['numerators'])
            score = np.sum((XALL @ a.T) / (1 + ZALL @ beta.T), axis=1)
            selected, labels, _ = choose_faces(score)
            v = beta / (1 - np.sum(abs(beta), axis=1, keepdims=True))
            round_best = [None]
            def fg(flat):
                if time.time() - start > args.seconds: raise TimeoutError
                v = flat.reshape(H, N); b, den = encode(v)
                fit = solve(b, signs, selected, labels)
                if fit is None: return 1e10, np.zeros_like(flat)
                g = fit.pop('gradient'); fit.pop('selected_next'); fit.pop('labels_next')
                if round_best[0] is None or fit['loss'] < round_best[0]['loss']:
                    round_best[0] = fit
                gv = (g - np.sum(g * v, axis=1, keepdims=True) *
                      v / np.sqrt(v*v + 1e-16) / den) / den
                return fit['loss'], gv.ravel()
            try:
                minimize(fg, v.ravel(), jac=True, method='L-BFGS-B',
                         options={'maxiter': args.iterations, 'maxls': 20, 'ftol': 1e-12})
            except TimeoutError:
                pass
            if round_best[0] is None: break
            best = round_best[0]; beta = np.array(best['beta'])
            best.update({'attempt': attempt, 'round': round_index, 'seconds': time.time() - start})
            with args.out.open('a') as out: out.write(json.dumps(best) + '\n')
            print({k: best[k] for k in ['attempt', 'round', 'loss', 'witness_count', 'witness_minimum', 'seconds']}, flush=True)
            if best['witness_count'] == 36:
                print('NUMERICAL WITNESS FOUND; EXACT CHECK REQUIRED', flush=True)
                return
            if time.time() - start > args.seconds: break


if __name__ == '__main__': main()
