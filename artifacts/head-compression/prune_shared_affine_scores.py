#!/usr/bin/env python3
"""Delete shared-chart units, refit numerators, and audit every accepted score.

Deletion distances only rank trials. They are not sign certificates or a
universal pruning theorem. Run large instances with heavy.
"""
import argparse
import json
import os
from pathlib import Path
import time

for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
import scipy.linalg as la
from search_shared_affine_varpro import initialize, features, exact_lift, Problem
from search_varpro_scores import convex_hinge_fit
from audit_rational_score import audit


def deletion_order(r, z, n, units):
    inverse = la.solve_triangular(r, np.eye(len(r)), check_finite=False)
    costs = []
    for h in range(units):
        block = inverse[n+1+h*n:n+1+(h+1)*n].T
        u, _ = la.qr(block, mode="economic", check_finite=False)
        costs.append(float(la.norm(u.T@z)**2))
    return np.argsort(costs), costs


def run(checkpoint, out, seconds, trial_seconds, target, batch):
    start = time.monotonic()
    labels, logs, separation, coefficient = initialize(checkpoint)
    units, n = logs.shape
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    events, attempt, accepted = [], 0, 0
    while len(logs)+1 > target and time.monotonic()-start < seconds:
        if (out/"STOP").exists():
            break
        matrix = features(x, logs, separation)
        q, r = la.qr(matrix, mode="economic", check_finite=False)
        fit = convex_hinge_fit(labels[:, None]*q, q.T@(matrix@coefficient),
                               "newton", 1e-9)
        order, costs = deletion_order(r, fit.x, n, len(logs))
        progress = False
        for number in sorted(set([min(batch, len(logs)+1-target), 1]), reverse=True):
            for offset in range(min(4, len(logs)//number)):
                if time.monotonic()-start >= seconds or (out/"STOP").exists():
                    break
                removed = np.sort(order[offset*number:(offset+1)*number])
                keep = np.ones(len(logs), dtype=bool)
                keep[removed] = False
                qq, rr = q.copy(), r.copy()
                for h in removed[::-1]:
                    qq, rr = la.qr_delete(qq, rr, n+1+int(h)*n, n,
                                          which="col", check_finite=False)
                trial = convex_hinge_fit(labels[:, None]*qq, qq.T@(q@fit.x),
                                         "newton", 0.)
                cc = la.solve_triangular(rr, trial.x, check_finite=False)
                trial_matrix = features(x, logs[keep], separation[keep])
                score = trial_matrix@cc
                margin = labels*score
                event = dict(attempt=attempt, seconds=time.monotonic()-start,
                             old_heads=len(logs)+1, trial_heads=int(keep.sum())+1,
                             removed=removed.tolist(),
                             projected_costs=[costs[h] for h in removed],
                             errors=int((margin <= 0).sum()),
                             minimum_margin=float(margin.min()),
                             direct_qr_discrepancy=float(np.max(np.abs(score-qq@trial.x))))
                print(json.dumps(event), flush=True)
                attempt += 1
                directory = out/f"trial-{attempt:04d}"
                directory.mkdir()
                ll, ss = logs[keep].copy(), separation[keep].copy()
                cert = None
                if margin.min() > 1e-4:
                    cert, check = exact_lift(labels, ll, ss, cc)
                    event["lift_check"] = check
                elif trial_seconds > 0:
                    p = Problem(labels, ll, ss, cc, directory,
                                min(trial_seconds, seconds-(time.monotonic()-start)))
                    p.run()
                    if p.certificate:
                        labels2, ll, ss, cc = initialize(directory/"checkpoint.npz")
                        assert np.array_equal(labels, labels2)
                        # Check the exact checkpoint being retained, even if a
                        # different objective evaluation caused termination.
                        cert, check = exact_lift(labels, ll, ss, cc)
                        event["retained_checkpoint_check"] = check
                if cert is not None:
                    path = directory/"certificate.json"
                    path.write_text(json.dumps(cert)+"\n")
                    report = audit(path, 224)
                    (directory/"exact-audit.json").write_text(json.dumps(report, indent=2)+"\n")
                    assert report["all_target_signs_certified"], report
                    logs, separation, coefficient = ll, ss, cc
                    np.savez(out/"latest.npz", labels=labels, logs=logs,
                             separation=separation, coefficients=coefficient,
                             kind="shared-affine")
                    (out/"certificate.json").write_text(json.dumps(cert)+"\n")
                    (out/"exact-audit.json").write_text(json.dumps(report, indent=2)+"\n")
                    event["accepted"] = True
                    accepted += number
                    progress = True
                else:
                    event["accepted"] = False
                events.append(event)
                (out/"events.json").write_text(json.dumps(events, indent=2)+"\n")
                print(json.dumps(event), flush=True)
                if progress:
                    break
            if progress:
                break
        if not progress:
            break
    result = dict(initial_heads=units+1, final_heads=len(logs)+1,
                  removed_units=accepted, seconds=time.monotonic()-start,
                  scope="One finite target only; failed deletion is not a lower bound.",
                  target_proved=False)
    (out/"result.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("checkpoint", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=36000)
    p.add_argument("--trial-seconds", type=float, default=1200)
    p.add_argument("--target", type=int, required=True)
    p.add_argument("--batch", type=int, default=4)
    a = p.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    run(a.checkpoint, a.out, a.seconds, a.trial_seconds, a.target, a.batch)
