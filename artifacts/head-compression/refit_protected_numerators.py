#!/usr/bin/env python3
"""Convex numerator refitting inside a protected rational-score sign region.

The denominators stay fixed. Each accepted damped Newton step must lower
both double and extended-precision objectives and retain all protected signs.
This is a finite numerical diagnostic, not a global or asymptotic theorem.
Run large instances through heavy.
"""
import argparse
import json
import os
from pathlib import Path
import time

for variable in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[variable] = '1'
import numpy as np
import scipy.linalg as la
import scipy.sparse.linalg as spla
from search_shared_affine_varpro import initialize, features
from search_shared_affine_gauss_newton import quick_score
from search_protected_barrier import barrier_terms, precise_score


def refit(x, labels, logs, separation, coefficient, protected, target,
          mu=.1, ridge=1e-6, steps=20, maxiter=100, seconds=1800,
          emit=None, basis=None, stop_path=None):
    started = time.monotonic()
    coefficient = coefficient.copy()
    if basis is None:
        feature = features(x, logs, separation)
        q, r = la.qr(feature, mode='economic', check_finite=False)
        del feature
    else:
        q, r = basis
    assert q.shape[1] == len(coefficient) and r.shape == (len(coefficient), len(coefficient))
    score = quick_score(x, logs, separation, coefficient)
    precise = precise_score(x, logs, separation, coefficient)
    assert np.min((labels*score)[protected]) > 0
    assert np.min((labels*precise)[protected]) > 0
    events = []
    for iteration in range(steps):
        if time.monotonic()-started >= seconds or (stop_path is not None and stop_path.exists()):
            break
        value, gradient, curvature = barrier_terms(labels, score, protected, target, mu, ridge)
        precise_value = barrier_terms(labels, precise, protected, target, mu, ridge)[0]
        scale = np.sqrt(np.einsum('ij,i,ij->j', q, curvature, q))
        scale = np.maximum(scale, max(float(np.median(scale))*1e-8, 1e-15))
        sqrt_w = np.sqrt(curvature)
        def forward(v):
            return sqrt_w*(q@(v/scale))
        def backward(v):
            return (q.T@(sqrt_w*v))/scale
        operator = spla.LinearOperator(q.shape, matvec=forward, rmatvec=backward, dtype=float)
        solved = spla.lsmr(operator, -gradient/sqrt_w, damp=1e-5,
                           atol=1e-9, btol=1e-9, maxiter=maxiter)
        response_q = solved[0]/scale
        delta = q@response_q
        derivative = float(gradient@delta)
        event = {'iteration': iteration, 'seconds': time.monotonic()-started,
                 'value': value, 'target': int(target), 'target_margin': float(labels[target]*score[target]),
                 'minimum_protected_margin': float(np.min((labels*score)[protected])),
                 'model_derivative': derivative, 'lsmr_stop': int(solved[1]),
                 'lsmr_iterations': int(solved[2]), 'gradient_norm': float(np.linalg.norm(q.T@gradient)),
                 'accepted': False}
        if not np.isfinite(derivative) or derivative >= 0:
            events.append(event)
            if emit: emit(event)
            break
        response = la.solve_triangular(r, response_q, check_finite=False)
        margin, dm = labels*score, labels*delta
        shrinking = protected & (dm < 0)
        alpha = min(1., .99*float(np.min(-margin[shrinking]/dm[shrinking]))) if shrinking.any() else 1.
        for _ in range(35):
            trial_c = coefficient+alpha*response
            trial_s = quick_score(x, logs, separation, trial_c)
            if np.min((labels*trial_s)[protected]) <= 1e-9:
                alpha *= .5
                continue
            trial_value = barrier_terms(labels, trial_s, protected, target, mu, ridge)[0]
            if trial_value >= value-max(1e-13, abs(value)*1e-11):
                alpha *= .5
                continue
            trial_p = precise_score(x, logs, separation, trial_c)
            if np.min((labels*trial_p)[protected]) <= 1e-9:
                alpha *= .5
                continue
            trial_precise_value = barrier_terms(labels, trial_p, protected, target, mu, ridge)[0]
            if trial_precise_value >= precise_value-max(1e-13, abs(precise_value)*1e-11):
                alpha *= .5
                continue
            coefficient, score, precise = trial_c, trial_s, trial_p
            event.update(accepted=True, alpha=alpha, value_after=trial_value,
                         extended_value_after=trial_precise_value,
                         target_margin_after=float(labels[target]*precise[target]),
                         minimum_protected_margin_after=float(np.min((labels*precise)[protected])),
                         score_discrepancy=float(np.max(np.abs(score-precise))))
            break
        events.append(event)
        if emit: emit(event)
        if not event['accepted'] or labels[target]*precise[target] > 1e-3:
            break
    return coefficient, score, events


def self_test(out):
    rng = np.random.default_rng(2026112207)
    n, units = 5, 2
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    logs, separation = rng.normal(size=(units, n)), np.array([.7, -.6])
    coefficient = rng.normal(size=n+1+n*units)
    score = quick_score(x, logs, separation, coefficient)
    labels = np.where(score > 0, 1., -1.)
    target = int(np.argmin(np.abs(score)))
    labels[target] *= -1
    protected = np.arange(len(x)) != target
    phi = features(x, logs, separation)
    direction = rng.normal(size=len(coefficient))
    delta = phi@direction
    value, gradient, curvature = barrier_terms(labels, score, protected, target, .1, 1e-6)
    eps = 1e-7
    plus = barrier_terms(labels, score+eps*delta, protected, target, .1, 1e-6)
    minus = barrier_terms(labels, score-eps*delta, protected, target, .1, 1e-6)
    grad_error = abs((plus[0]-minus[0])/(2*eps)-gradient@delta)
    hess_error = float(np.max(np.abs((plus[1]-minus[1])/(2*eps)-curvature*delta)))
    assert grad_error < 1e-6 and hess_error < 1e-5
    cc, ss, events = refit(x, labels, logs, separation, coefficient, protected, target,
                           steps=10, maxiter=100, seconds=60)
    assert events and any(event['accepted'] for event in events)
    assert (labels*ss)[protected].min() > 0
    assert barrier_terms(labels, ss, protected, target, .1, 1e-6)[0] < value
    q, r = la.qr(phi, mode='economic', check_finite=False)
    reused_c, reused_s, reused_events = refit(x, labels, logs, separation, coefficient,
        protected, target, steps=10, maxiter=100, seconds=60, basis=(q, r))
    reuse_error = float(np.max(np.abs(reused_s-ss)))
    assert reuse_error < 1e-9 and reused_events
    np.savez(out/'seed.npz', labels=labels, logs=logs, separation=separation,
             coefficients=coefficient, kind='shared-affine')
    result = {'n': n, 'units': units, 'gradient_error': float(grad_error),
              'basis_reuse_score_error': reuse_error, 'hessian_direction_error': hess_error, 'initial_target_margin': float(labels[target]*score[target]),
              'final_target_margin': float(labels[target]*ss[target]), 'events': events,
              'scope': 'Finite numerical check only; no target theorem or global convergence assertion.'}
    (out/'self-test.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkpoint', nargs='?', type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--steps', type=int, default=20)
    parser.add_argument('--maxiter', type=int, default=100)
    parser.add_argument('--seconds', type=float, default=1800)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.self_test:
        self_test(args.out)
    else:
        labels, logs, separation, cc = initialize(args.checkpoint)
        x = ((np.arange(len(labels))[:, None] >> np.arange(logs.shape[1])) & 1).astype(float)
        initial = precise_score(x, logs, separation, cc)
        protected = labels*initial > 0
        remaining = np.flatnonzero(~protected)
        assert len(remaining)
        target = int(remaining[np.argmax((labels*initial)[remaining])])
        np.savez(args.out/'initial.npz', labels=labels, logs=logs, separation=separation,
                 coefficients=cc, kind='shared-affine')
        cc, score, events = refit(x, labels, logs, separation, cc, protected, target,
            steps=args.steps, maxiter=args.maxiter, seconds=args.seconds,
            emit=lambda event: print(json.dumps(event), flush=True))
        np.savez(args.out/'checkpoint.npz', labels=labels, logs=logs, separation=separation,
                 coefficients=cc, kind='shared-affine')
        result = {'n': logs.shape[1], 'heads_after_lift': logs.shape[0]+1,
                  'target': target, 'initial_protected': int(protected.sum()),
                  'final_errors': int((labels*score <= 0).sum()), 'events': events,
                  'certificate': None, 'scope': 'Numerator-only numerical continuation diagnostic.'}
        (args.out/'result.json').write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps({k: v for k, v in result.items() if k != 'events'}), flush=True)
