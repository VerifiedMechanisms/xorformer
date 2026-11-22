#!/usr/bin/env python3
"""Propose exact dual witnesses for a fixed-residual pair replacement.

Run with heavy. Numerical optimization is used only to propose support and
weights. An independent rational-interval verifier certifies every output.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import sys
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[key] = '1'
import numpy as np
from scipy.optimize import linprog
import sympy as sp
from search_pair_completion import values
from verify_completion_witness import verify

sys.set_int_max_str_digits(0)


def reconstruct(matrix, target, approximate):
    """Project rounded free coordinates onto the exact affine moment space."""
    m = sp.Matrix(matrix.tolist())
    b = sp.Matrix(target.tolist())
    pivots = list(m.rref()[1])
    free = [i for i in range(m.cols) if i not in pivots]
    selected = m[:, pivots]
    rows = list(selected.T.rref()[1])
    inverse = selected[rows, :].inv()
    for digits in (12, 16, 20, 30, 50):
        denominator = 10 ** digits
        vector = sp.zeros(m.cols, 1)
        for i in free:
            value = Fraction(float(approximate[i]))
            rounded = round(value * denominator)
            vector[i] = sp.Rational(rounded, denominator)
        rhs = b - m * vector
        solution = inverse * rhs[rows, :]
        for i, value in zip(pivots, solution):
            vector[i] = value
        if m * vector == b and all(v >= 0 for v in vector) and any(v > 0 for v in vector):
            return [[int(v.p), int(v.q)] for v in vector]
    return None


def run(source, omitted, out, lp_seconds):
    data = json.loads(source.read_text())
    x, pieces, score = values(data)
    residual = score - pieces[:, omitted].sum(axis=1) if omitted else score
    labels = np.asarray(data['labels'])
    n = data['n']
    scale = float(max(1, np.max(np.abs(residual))))
    rr = np.asarray(residual / scale, dtype=float)
    results = []
    for orientation in (1, -1):
        z = np.column_stack((np.ones(len(x), dtype=int), np.asarray(x, dtype=int)))
        if orientation < 0:
            z[:, 1:] = 1 - z[:, 1:]
        matrix = np.column_stack((-labels[:, None] * z,
                                  -(labels * rr)[:, None] * z,
                                  np.ones(len(x))))
        fit = linprog(np.r_[np.zeros(2 * (n + 1)), -1.],
            A_ub=matrix, b_ub=np.zeros(len(x)),
            A_eq=np.r_[np.zeros(n + 1), np.ones(n + 1), 0.][None], b_eq=[1.],
            bounds=[(None, None)] * (n + 1) + [(0, None)] * (n + 1) + [(None, None)],
            method='highs', options={'time_limit': lp_seconds,
                'primal_feasibility_tolerance': 1e-10, 'dual_feasibility_tolerance': 1e-10})
        event = {'orientation': orientation, 'status': int(fit.status),
                 'message': fit.message, 'witness': None}
        if fit.status == 0:
            event['numerical_cleared_slack'] = float(fit.x[-1])
            approximate = -fit.ineqlin.marginals
            weights = None
            for cutoff in (1e-14, 1e-12, 1e-10, 1e-8):
                support = np.flatnonzero(approximate > cutoff)
                affine = (labels[:, None] * z)[support].T
                moments = np.vstack((np.ones(len(support), dtype=int), affine))
                target = np.r_[1, np.zeros(n + 1, dtype=int)]
                weights = reconstruct(moments, target, approximate[support])
                if weights is not None:
                    break
            if weights is not None:
                nonzero = [(v, w) for v, w in zip(support, weights) if w[0] > 0]
                cert = {'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                    'omitted_heads': omitted, 'orientation': orientation,
                    'weights': [{'vertex': int(v), 'weight': w} for v, w in nonzero],
                    'scope': 'Fixed residual only; retained heads cannot change.'}
                candidate = out / f'candidate-{orientation}.json'
                candidate.write_text(json.dumps(cert, indent=2) + '\n')
                try:
                    checked = verify(source, candidate)
                except AssertionError:
                    event['exact_verification_failed'] = True
                else:
                    path = out / f'witness-{orientation}.json'
                    candidate.rename(path)
                    (out / f'audit-{orientation}.json').write_text(json.dumps(checked, indent=2) + '\n')
                    event['witness'] = path.name
                    event['support'] = len(nonzero)
        results.append(event)
        print(json.dumps(event), flush=True)
    (out / 'result.json').write_text(json.dumps({'results': results,
        'scope': 'A restricted fixed-residual obstruction only.'}, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--omitted', type=int, nargs='*', default=[])
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--lp-seconds', type=float, default=300)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.source, args.omitted, args.out, args.lp_seconds)
