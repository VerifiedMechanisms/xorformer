#!/usr/bin/env python3
"""Try denominator coalescence before refitting a smaller anchored score.

Same-orientation denominator pairs are ranked by log-coefficient distance.
For each candidate, replace both denominators by their geometric midpoint
and measure the old score's distance to the resulting feature span. Refit
the best measured candidate, then adapt its denominators. A successful
ordinary rational certificate is checked independently. No universal
merging theorem or infeasibility conclusion is asserted.
"""
import argparse
import json
import os
from pathlib import Path
import time

for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[key] = '1'
import numpy as np
import scipy.linalg as la
from search_anchored_affine_varpro import from_shared, features, Problem
from search_varpro_scores import convex_hinge_fit
from audit_rational_score import audit


def merged_geometry(logs, orientation, i, j):
    assert i < j and orientation[i] == orientation[j]
    keep = np.ones(len(logs), dtype=bool)
    keep[[i, j]] = False
    return (np.concatenate((logs[keep], ((logs[i] + logs[j]) / 2)[None])),
            np.concatenate((orientation[keep], orientation[i:i+1])))


def merge_qr(q, r, x, logs, orientation, i, j):
    n = logs.shape[1]
    qq, rr = q.copy(), r.copy()
    for h in (j, i):
        qq, rr = la.qr_delete(qq, rr, n + 1 + h * n, n, which='col',
                              overwrite_qr=True, check_finite=False)
    ll, oo = merged_geometry(logs, orientation, i, j)
    tt = np.where(oo[-1] > 0, x[:, None], 1 - x[:, None])
    new_columns = features(x, tt, ll[-1:])[:, n + 1:]
    qq, rr = la.qr_insert(qq, rr, new_columns, rr.shape[1], which='col',
                         rcond=1e-16, overwrite_qru=True, check_finite=False)
    return qq, rr, ll, oo


def self_test():
    rng = np.random.default_rng(2026112217)
    n = 6
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    logs = rng.normal(size=(3, n))
    orientation = np.array([1, -1, 1])
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    matrix = features(x, t, logs)
    q, r = la.qr(matrix, mode='economic')
    qq, rr, ll, oo = merge_qr(q, r, x, logs, orientation, 0, 2)
    tt = np.where(oo[None, :, None] > 0, x[:, None], 1-x[:, None])
    target = features(x, tt, ll)
    error = float(np.max(np.abs(qq @ rr - target)))
    assert error < 1e-12
    assert float(np.max(np.abs(qq.T @ qq - np.eye(rr.shape[0])))) < 1e-12
    coefficient = rng.normal(size=n + 1 + 3*n)
    logs[2] = logs[0]
    original = features(x, t, logs) @ coefficient
    ll, oo = merged_geometry(logs, orientation, 0, 2)
    tt = np.where(oo[None, :, None] > 0, x[:, None], 1-x[:, None])
    blocks = coefficient[n+1:].reshape(3, n)
    merged = np.concatenate((coefficient[:n+1], blocks[1], blocks[0]+blocks[2]))
    equality_error = float(np.max(np.abs(features(x, tt, ll) @ merged - original)))
    assert equality_error < 1e-12
    return {'qr_reconstruction_error': error,
            'identical_denominator_merge_error': equality_error,
            'scope': 'Implementation identities only; no universal theorem.'}


def run(checkpoint, out, candidates, seconds):
    start = time.monotonic()
    labels, orientation, logs, coefficient = from_shared(checkpoint)
    units, n = logs.shape
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    matrix = features(x, t, logs)
    score = matrix @ coefficient
    q, r = la.qr(matrix, mode='economic', check_finite=False)
    del matrix
    choices = sorted((float(np.linalg.norm(logs[i]-logs[j])), i, j)
                     for i in range(units) for j in range(i+1, units)
                     if orientation[i] == orientation[j])[:candidates]
    records = []
    best = None
    for distance, i, j in choices:
        if (out/'STOP').exists() or time.monotonic()-start >= seconds:
            break
        try:
            qq, rr, ll, oo = merge_qr(q, r, x, logs, orientation, i, j)
        except la.LinAlgError as error:
            record = {'pair': [i, j], 'rank_update_failed': str(error)}
        else:
            residual = score - qq @ (qq.T @ score)
            cost = float(residual @ residual)
            record = {'pair': [i, j], 'log_distance': distance,
                      'score_projection_cost': cost,
                      'seconds': time.monotonic()-start}
            if best is None or cost < best[0]:
                best = (cost, i, j)
            del qq, rr, ll, oo, residual
        records.append(record)
        print(json.dumps(record), flush=True)
        (out/'merge-candidates.json').write_text(json.dumps(records, indent=2)+'\n')
    if best is None:
        result = {'termination': 'No valid candidate within this finite trial',
                  'certificate': None, 'failure_is_not_a_lower_bound': True}
        (out/'result.json').write_text(json.dumps(result)+'\n')
        return
    _, i, j = best
    qq, rr, ll, oo = merge_qr(q, r, x, logs, orientation, i, j)
    del q, r
    fit = convex_hinge_fit(labels[:, None]*qq, qq.T @ score, 'newton', 0.)
    cc = la.solve_triangular(rr, fit.x, check_finite=False)
    record = {'stage': 'merged_refit', 'pair': [i, j],
              'trial_heads': len(ll)+1, 'loss': float(fit.fun),
              'errors': int((labels*(qq@fit.x) <= 0).sum()),
              'seconds': time.monotonic()-start}
    print(json.dumps(record), flush=True)
    (out/'initial-refit.json').write_text(json.dumps(record, indent=2)+'\n')
    np.savez(out/'initial.npz', labels=labels, orientation=oo, logs=ll,
             coefficients=cc, kind='anchored-affine')
    del qq, rr
    problem = Problem(labels, oo, ll, cc, out, max(0., seconds-(time.monotonic()-start)))
    problem.run()
    if problem.certificate:
        report = audit(out/problem.certificate, 224)
        (out/'independent-audit.json').write_text(json.dumps(report, indent=2)+'\n')
        assert report['all_target_signs_certified']


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('checkpoint', nargs='?', type=Path)
    p.add_argument('--out', required=True, type=Path)
    p.add_argument('--self-test', action='store_true')
    p.add_argument('--candidates', type=int, default=8)
    p.add_argument('--seconds', type=float, default=5400)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.self_test:
        result = self_test()
        (args.out/'self-test.json').write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps(result))
    else:
        assert args.checkpoint is not None and args.candidates > 0
        run(args.checkpoint, args.out, args.candidates, args.seconds)
