#!/usr/bin/env python3
"""Rank a single batch deletion, refit, then optimize the anchored chart.

The ranking is the exact linear projection formula evaluated numerically.
Only a separately audited rational certificate establishes a smaller count.
This is one finite target experiment, not a universal pruning theorem.
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
from search_anchored_affine_varpro import from_shared, features, score_gradient, Problem
from prune_shared_affine_scores import deletion_order
from search_varpro_scores import convex_hinge_fit
from audit_rational_score import audit


def run(checkpoint, out, batch, seconds):
    start = time.monotonic()
    labels, orientation, logs, coefficient = from_shared(checkpoint)
    units, n = logs.shape
    assert 0 < batch < units
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    matrix = features(x, t, logs)
    q, r = la.qr(matrix, mode="economic", check_finite=False)
    z = q.T@(matrix@coefficient)
    order, costs = deletion_order(r, z, n, units)
    removed = np.sort(order[:batch])
    keep = np.ones(units, dtype=bool)
    keep[removed] = False
    before = {"stage": "ranked", "initial_heads": units+1,
              "trial_heads": units+1-batch, "removed": removed.tolist(),
              "projection_costs": [costs[h] for h in removed],
              "seconds": time.monotonic()-start}
    print(json.dumps(before), flush=True)
    (out/"deletion.json").write_text(json.dumps(before, indent=2)+"\n")
    for h in removed[::-1]:
        q, r = la.qr_delete(q, r, n+1+int(h)*n, n, which="col", check_finite=False)
    old_score = matrix@coefficient
    del matrix
    fit = convex_hinge_fit(labels[:, None]*q, q.T@old_score, "newton", 0.)
    cc = la.solve_triangular(r, fit.x, check_finite=False)
    ll, oo = logs[keep], orientation[keep]
    loss, score, _ = score_gradient(x, t[:, keep], labels, ll, cc)
    record = {"stage": "refitted", "loss": loss, "errors": int((labels*score <= 0).sum()),
              "minimum_margin": float((labels*score).min()),
              "inner_gradient": float(np.max(np.abs(fit.jac))),
              "direct_qr_discrepancy": float(np.max(np.abs(score-q@fit.x))),
              "seconds": time.monotonic()-start}
    print(json.dumps(record), flush=True)
    (out/"initial-refit.json").write_text(json.dumps(record, indent=2)+"\n")
    np.savez(out/"initial.npz", labels=labels, orientation=oo, logs=ll,
             coefficients=cc, kind="anchored-affine")
    problem = Problem(labels, oo, ll, cc, out, max(0., seconds-(time.monotonic()-start)))
    problem.run()
    if problem.certificate:
        report = audit(out/problem.certificate, 224)
        (out/"independent-audit.json").write_text(json.dumps(report, indent=2)+"\n")
        assert report["all_target_signs_certified"], report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--batch", type=int, required=True)
    parser.add_argument("--seconds", type=float, default=3600)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.batch, args.seconds)
