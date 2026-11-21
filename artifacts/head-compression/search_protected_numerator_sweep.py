#!/usr/bin/env python3
"""Try successive protected-sign extensions with one fixed denominator list.

Reuses the expensive QR factorization across targets. Failed target steps
are not infeasibility certificates. Only an independently checked full-cube
rational score counts as a finite representation. Run through heavy.
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
from search_shared_affine_varpro import initialize, features, exact_lift
from search_protected_barrier import precise_score
from refit_protected_numerators import refit


def run(checkpoint, out, seconds, steps, maxiter, mu, ridge):
    started = time.monotonic()
    stop = out/'STOP'
    labels, logs, separation, coefficient = initialize(checkpoint)
    units, n = logs.shape
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    precise = precise_score(x, logs, separation, coefficient)
    protected = labels*precise > 0
    initial_protected = int(protected.sum())
    feature = features(x, logs, separation)
    q, r = la.qr(feature, mode='economic', check_finite=False)
    del feature
    basis = q, r
    attempted, events, certificate = set(), [], None
    def save(name):
        np.savez(out/name, labels=labels, logs=logs, separation=separation,
                 coefficients=coefficient, kind='shared-affine')
    save('initial.npz')
    while time.monotonic()-started < seconds and not stop.exists():
        precise = precise_score(x, logs, separation, coefficient)
        margin = labels*precise
        assert margin[protected].min() > 0
        protected |= margin > 1e-3
        if protected.all():
            save('checkpoint.npz')
            cert, check = exact_lift(labels, logs, separation, coefficient)
            if cert is not None:
                (out/'certificate.json').write_text(json.dumps(cert)+'\n')
                certificate = 'certificate.json'
            else:
                events.append({'export_failure': check})
            break
        remaining = np.array([int(i) for i in np.flatnonzero(~protected) if int(i) not in attempted])
        if not len(remaining):
            break
        target = int(remaining[np.argmax(margin[remaining])])
        attempted.add(target)
        old_count = int(protected.sum())
        event = {'phase': 'target_start', 'seconds': time.monotonic()-started,
                 'target': target, 'protected_vertices': old_count,
                 'target_margin': float(margin[target]), 'mu': mu, 'ridge': ridge}
        print(json.dumps(event), flush=True)
        coefficient, score, inner = refit(x, labels, logs, separation, coefficient,
            protected, target, mu=mu, ridge=ridge, steps=steps, maxiter=maxiter,
            seconds=seconds-(time.monotonic()-started), basis=basis, stop_path=stop,
            emit=lambda item: print(json.dumps({'phase': 'inner', **item}), flush=True))
        precise = precise_score(x, logs, separation, coefficient)
        margin = labels*precise
        assert margin[protected].min() > 0
        protected |= margin > 1e-3
        promoted = int(protected.sum())-old_count
        event.update(phase='target_complete', seconds=time.monotonic()-started,
                     protected_vertices=int(protected.sum()), promoted=promoted,
                     target_margin_after=float(margin[target]), inner_steps=len(inner),
                     minimum_protected_margin=float(margin[protected].min()))
        events.append(event)
        print(json.dumps(event), flush=True)
        save('latest.npz')
        if promoted:
            save('checkpoint.npz')
            attempted.clear()
    result = {'n': n, 'heads_after_lift': units+1, 'seconds': time.monotonic()-started,
              'initial_protected': initial_protected, 'final_protected': int(protected.sum()),
              'certificate': certificate, 'events': events,
              'scope': 'One fixed list of denominators and one truth table only. No universal bound.',
              'failure_is_not_a_lower_bound': True}
    (out/'result.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'events'}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkpoint', type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--seconds', type=float, default=3600)
    parser.add_argument('--steps', type=int, default=25)
    parser.add_argument('--maxiter', type=int, default=150)
    parser.add_argument('--mu', type=float, default=.1)
    parser.add_argument('--ridge', type=float, default=1e-6)
    args = parser.parse_args()
    assert min(args.seconds, args.steps, args.maxiter, args.mu, args.ridge) > 0
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.seconds, args.steps, args.maxiter, args.mu, args.ridge)
