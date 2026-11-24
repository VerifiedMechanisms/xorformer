"""Mass minimization for a three/four-head top-degree coefficient seed."""
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


class Problem:
    def __init__(self, heads, k):
        self.h = heads
        self.m = 2 * heads
        widths = [6, 2, 3] if heads == 3 else [8, 2, 2, 2]
        self.n = sum(widths)
        self.k = np.asarray(k, dtype=float)
        offsets = np.cumsum([0] + widths)
        self.groups = [list(range(offsets[j], offsets[j + 1])) for j in range(heads)]
        columns = list(itertools.product(*self.groups[1:]))
        assert len(columns) == self.m
        self.axes = np.array([[(i,) + column for column in columns] for i in self.groups[0]])
        self.weights = []
        for i in range(self.m):
            for j in range(self.m):
                if i != j:
                    w = np.zeros((self.m, self.m)); w[i, j] = 1; self.weights.append(w)
        for j in range(self.m):
            w = np.zeros((self.m, self.m)); w[:, j] = -1; self.weights.append(w)

    def coefficients(self, b):
        a = np.zeros((self.m, self.m, self.h * self.n + 1))
        rows, cols = np.indices((self.m, self.m))
        for order in itertools.permutations(range(self.h)):
            term = np.ones((self.m, self.m))
            for h, position in enumerate(order):
                term *= b[h, self.axes[:, :, position]]
            a[:, :, -1] += term
        for h in range(self.h):
            others = [g for g in range(self.h) if g != h]
            for position in range(self.h):
                remaining = [p for p in range(self.h) if p != position]
                term = np.zeros((self.m, self.m))
                for order in itertools.permutations(remaining):
                    piece = np.ones((self.m, self.m))
                    for g, p in zip(others, order):
                        piece *= b[g, self.axes[:, :, p]]
                    term += piece
                a[rows, cols, h * self.n + self.axes[:, :, position]] = self.k[h] * term
        return a

    def derivative(self, b, s, lam, weights):
        bt = torch.tensor(b, requires_grad=True)
        kt = torch.tensor(self.k, requires_grad=True)
        c = torch.zeros((self.m, self.m))
        for order in itertools.permutations(range(self.h)):
            term = torch.ones((self.m, self.m))
            for h, position in enumerate(order):
                term = term * bt[h, self.axes[:, :, position]]
            c = c + lam * term
        for h in range(self.h):
            others = [g for g in range(self.h) if g != h]
            for position in range(self.h):
                remaining = [p for p in range(self.h) if p != position]
                term = torch.zeros((self.m, self.m))
                for order in itertools.permutations(remaining):
                    piece = torch.ones((self.m, self.m))
                    for g, p in zip(others, order):
                        piece = piece * bt[g, self.axes[:, :, p]]
                    term = term + piece
                c = c + kt[h] * torch.tensor(s[h, self.axes[:, :, position]]) * term
        torch.sum(torch.tensor(weights) * c).backward()
        return bt.grad.numpy(), kt.grad.numpy()

    def solve(self, b, delta):
        hn = self.h * self.n
        a = self.coefficients(b)
        matrix = np.zeros((len(self.weights) + self.h, hn + 4))
        for i, w in enumerate(self.weights):
            matrix[i, :hn + 1] = np.einsum('ij,ijv->v', w, a)
        for h in range(self.h):
            matrix[len(self.weights) + h, h * self.n:(h + 1) * self.n] = 1
            matrix[len(self.weights) + h, hn + 1] = -1
        rhs = np.r_[np.full(len(self.weights), -delta), np.zeros(self.h)]
        objective = np.zeros(hn + 4); objective[hn + 1] = 1; objective[hn + 2:] = 1e-5
        eq = np.zeros((1, hn + 4)); eq[0, hn] = 1; eq[0, hn + 2] = -1; eq[0, hn + 3] = 1
        bounds = [(abs(v) + 1e-5, None) for v in b.ravel()] + [(None, None)] + [(0, None)] * 3
        result = linprog(objective, A_ub=matrix, b_ub=rhs, A_eq=eq, b_eq=[0],
                         bounds=bounds, method='highs', options={'time_limit': 3.})
        if not result.success:
            return None
        s, lam = result.x[:hn].reshape(self.h, self.n), result.x[hn]
        mu = -result.ineqlin.marginals[:len(self.weights)]
        weights = sum(w * value for w, value in zip(self.weights, mu))
        grad, grad_k = self.derivative(b, s, lam, weights)
        grad += result.lower.marginals[:hn].reshape(self.h, self.n) * np.sign(b)
        scale = 1 / (1 + s.sum(axis=1))
        bn, sn = b * scale[:, None], s * scale[:, None]
        c = np.einsum('ijv,v->ij', self.coefficients(bn), np.r_[sn.ravel(), lam])
        record = {'objective': float(result.fun), 'beta': bn.tolist(), 'mass': sn.tolist(),
                  'k': self.k.tolist(), 'constant': float(lam), 'C': c.tolist(),
                  'beta_l1': abs(bn).sum(axis=1).tolist(),
                  'offmax': float(c[~np.eye(self.m, dtype=bool)].max()),
                  'colmin': float(c.sum(axis=0).min()),
                  'status': 'numerical coefficient relaxation only'}
        return result.fun, grad, grad_k, record


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed-file', required=True, type=Path)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--iterations', type=int, default=100)
    ap.add_argument('--seconds', type=int, default=120)
    ap.add_argument('--restarts', type=int, default=4)
    ap.add_argument('--delta', type=float, default=1e-8)
    ap.add_argument('--variable-k', action='store_true')
    args = ap.parse_args()
    seed = json.loads(args.seed_file.read_text())
    b0 = np.array(seed.get('b', seed.get('beta')))
    b0 /= np.sum(abs(b0), axis=1, keepdims=True)
    k = np.array(seed.get('k', seed.get('signs')))
    k /= abs(k).max()
    problem = Problem(len(k), k)
    rng = np.random.default_rng(161803)
    for restart in range(args.restarts):
        start, best, last_print = time.time(), [None], [float('inf')]
        bstart = b0 + (rng.normal(size=b0.shape) * 1e-5 if restart else 0)
        ksign = np.sign(k)
        initial = np.r_[bstart.ravel(), np.log(abs(k))] if args.variable_k else bstart.ravel()
        def fg(flat):
            if time.time() - start > args.seconds:
                raise TimeoutError
            v = flat[:b0.size].reshape(b0.shape)
            if args.variable_k:
                logits = flat[b0.size:]
                weights = np.exp(logits - logits.max())
                weights /= weights.sum()
                problem.k = ksign * weights
            norm = np.sum(abs(v), axis=1, keepdims=True)
            b = v / norm
            result = problem.solve(b, args.delta)
            if result is None:
                return 1e12, np.zeros_like(flat)
            value, grad, grad_k, record = result
            if best[0] is None or value < best[0]['objective']:
                best[0] = record
                args.out.with_suffix('.checkpoint.json').write_text(json.dumps(record))
                if value < last_print[0] * .99:
                    last_print[0] = value
                    print({'restart': restart, 'objective': value,
                           'beta_l1': record['beta_l1'], 'seconds': time.time() - start}, flush=True)
            gradient = (grad - np.sum(grad * b, axis=1, keepdims=True) * np.sign(v)) / norm
            if args.variable_k:
                gradient_k = grad_k * problem.k - weights * np.sum(grad_k * problem.k)
                return value, np.r_[gradient.ravel(), gradient_k]
            return value, gradient.ravel()
        try:
            minimize(fg, initial, jac=True, method='L-BFGS-B',
                     options={'maxiter': args.iterations, 'maxls': 20, 'ftol': 1e-12})
        except TimeoutError:
            pass
        if best[0] is not None:
            best[0].update({'restart': restart, 'seconds': time.time() - start})
            with args.out.open('a') as out:
                out.write(json.dumps(best[0]) + '\n')
