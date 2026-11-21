#!/usr/bin/env python3
"""Discrete pole-routing search on a finite promised decoder grid.

Only the assignment of an existing pole multiset to a fixed residue
dictionary changes. This does not prove a universal decoder or a full-cube
construction. Run through heavy. Successful candidates use an independent
exact rational checker.
"""
import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import time
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[key] = '1'
import numpy as np
from refit_high_precision import exact_midpoint
from search_cauchy_smooth import fit
from verify_cauchy_grid import verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=10800)
    parser.add_argument('--bits', type=int, default=1024)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    data = np.load(args.checkpoint)
    sigma, labels, initial = data['sigma'], data['labels'], data['logs']
    m, k = labels.shape
    h = len(initial)
    rng = np.random.default_rng(270000+k)
    start = time.monotonic()
    current = initial.copy()
    best_logs = current.copy()
    best = current_loss = float('inf')
    iteration = accepted = rejected = 0
    while time.monotonic()-start < args.seconds:
        candidate = current.copy()
        if iteration and iteration % 160 == 0:
            candidate = best_logs.copy()
            rng.shuffle(candidate)
        elif iteration:
            for _ in range(1 if iteration % 12 else 4):
                i, j = rng.choice(h, 2, replace=False)
                if np.array_equal(sigma[i], sigma[j]):
                    continue
                candidate[i], candidate[j] = candidate[j], candidate[i]
        try:
            loss, _, a, b, margins, inner = fit(candidate, sigma, labels, args.bits)
        except ArithmeticError:
            rejected += 1
            iteration += 1
            continue
        temperature = .002*(.05**((iteration % 160)/160))
        if loss < current_loss or rng.random() < np.exp(min(0, (current_loss-loss)/temperature)):
            current, current_loss = candidate, loss
            accepted += 1
        if loss < best:
            best, best_logs = loss, candidate.copy()
            np.savez(args.out/'checkpoint.npz', logs=candidate, sigma=sigma, labels=labels)
            print(json.dumps({'iteration': iteration, 'seconds': time.monotonic()-start,
                'loss': loss, 'errors': int((margins <= 0).sum()),
                'accepted': accepted, 'rejected': rejected, 'inner_gradient': inner}), flush=True)
        if margins.min() > 1e-6:
            aa = [exact_midpoint(a[t, 0]) for t in range(h)]
            exact = [int(labels[p-1, j])*sum((4*aa[t]*b[t]*int(sigma[t, j])/(p+b[t])**2
                for t in range(h)), Fraction(0)) for p in range(1, m+1) for j in range(k)]
            if min(exact) <= 0:
                raise ArithmeticError('independent exact signs failed')
            margin = min(exact)
            path = args.out/'certificate.json'
            path.write_text(json.dumps({'a': [[v.numerator, v.denominator] for v in aa],
                'b': [[v.numerator, v.denominator] for v in b],
                'labels': labels.tolist(), 'sigma': sigma.tolist(),
                'margin': [margin.numerator, margin.denominator],
                'scope': 'Finite promised-grid signs only.'})+'\n')
            print(json.dumps(verify(path)), flush=True)
            break
        iteration += 1
    print(json.dumps({'seconds': time.monotonic()-start, 'iterations': iteration,
        'best_loss': best, 'target_proved': False}), flush=True)


if __name__ == '__main__':
    main()
