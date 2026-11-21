#!/usr/bin/env python3
"""Incremental sign constraints in the shared-affine rational chart.

Start from the vertices already classified correctly, introduce a small batch
of remaining vertices, and refit all protected constraints before adding more.
Failed stages roll back and reduce the batch. This is a finite numerical probe,
not a proof of extension, global convergence, or universal head complexity.
Only an exact full-cube certificate is reported as success. Use heavy.
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
import scipy.optimize as opt
from search_shared_affine_varpro import (
    initialize, unpack, features, score_gradient, exact_lift)
from search_varpro_scores import convex_hinge_fit


class StageComplete(Exception):
    pass


class BudgetExpired(Exception):
    pass


class Curriculum:
    def __init__(self, checkpoint, out, seconds, stage_seconds, batch, seed):
        labels, logs, separation, coefficient = initialize(checkpoint)
        self.y, self.units, self.n = labels, *logs.shape
        self.x = ((np.arange(len(labels))[:, None] >> np.arange(self.n)) & 1).astype(float)
        self.parameters = np.r_[logs.ravel(), separation]
        self.coefficient = coefficient
        self.out, self.start = out, time.monotonic()
        self.deadline = self.start+seconds
        self.stage_seconds, self.batch = stage_seconds, batch
        self.rng = np.random.default_rng(seed)
        self.events, self.stages = [], []
        self.best, self.certificate = None, None
        score = score_gradient(self.x, self.y, logs, separation, coefficient)[1]
        self.protected = self.y*score > 1e-4
        assert self.protected.sum() > len(coefficient), "Need enough protected rows for full-column QR."
        self.original_protected = int(self.protected.sum())

    def save(self, name, parameters, coefficient):
        logs, separation = unpack(parameters, self.units, self.n)
        np.savez(self.out/name, labels=self.y, logs=logs, separation=separation,
                 coefficients=coefficient, kind="shared-affine")

    def objective(self, parameters):
        now = time.monotonic()
        if now >= self.deadline or now >= self.stage_deadline or (self.out/"STOP").exists():
            raise BudgetExpired
        logs, separation = unpack(parameters, self.units, self.n)
        xx, yy = self.x[self.selected], self.y[self.selected]
        feature = features(xx, logs, separation)
        q, r = la.qr(feature, mode="economic", check_finite=False)
        initial = q.T@(feature@self.previous)
        fit = convex_hinge_fit(yy[:, None]*q, initial, "newton", 0.)
        coefficient = la.solve_triangular(r, fit.x, check_finite=False)
        loss, partial_score, gradient = score_gradient(xx, yy, logs, separation, coefficient)
        discrepancy = float(np.max(np.abs(partial_score-q@fit.x)))
        full_loss, score, _ = score_gradient(self.x, self.y, logs, separation, coefficient)
        margin = self.y*score
        self.previous = coefficient
        self.last = parameters.copy(), coefficient.copy(), margin.copy()
        event = {"stage": len(self.stages), "evaluation": len(self.events),
                 "seconds": time.monotonic()-self.start,
                 "selected_vertices": int(self.selected.sum()),
                 "protected_vertices": int(self.protected.sum()),
                 "selected_loss": loss, "full_loss": full_loss,
                 "selected_errors": int((margin[self.selected] <= 0).sum()),
                 "full_errors": int((margin <= 0).sum()),
                 "selected_minimum_margin": float(margin[self.selected].min()),
                 "full_minimum_margin": float(margin.min()),
                 "direct_qr_score_discrepancy": discrepancy,
                 "inner_gradient": float(np.max(np.abs(fit.jac)))}
        self.events.append(event)
        print(json.dumps(event), flush=True)
        metric = event["full_errors"], full_loss
        if self.best is None or metric < self.best:
            self.best = metric
            self.save("checkpoint.npz", parameters, coefficient)
        if margin.min() > 1e-5:
            cert, check = exact_lift(self.y, logs, separation, coefficient)
            event["exact_check"] = check
            if cert is not None:
                (self.out/"certificate.json").write_text(json.dumps(cert)+"\n")
                self.certificate = "certificate.json"
                raise StageComplete
        # The direct score, not Q times the inner solution, controls promotion.
        # This is only a numerical stage test; it is never an exact certificate.
        if event["selected_minimum_margin"] > max(1e-4, 100*discrepancy):
            raise StageComplete
        return loss, gradient

    def run(self):
        consecutive_failures = 0
        while time.monotonic() < self.deadline and not (self.out/"STOP").exists():
            logs, separation = unpack(self.parameters, self.units, self.n)
            current_score = score_gradient(self.x, self.y, logs, separation, self.coefficient)[1]
            margin = self.y*current_score
            assert margin[self.protected].min() > 0
            remaining = np.flatnonzero(~self.protected)
            if not len(remaining):
                cert, check = exact_lift(self.y, logs, separation, self.coefficient)
                if cert is not None:
                    (self.out/"certificate.json").write_text(json.dumps(cert)+"\n")
                    self.certificate = "certificate.json"
                break
            count = min(self.batch, len(remaining))
            # Normally add the closest failures. After a failed stage change
            # its batch, instead of silently relaxing protected constraints.
            if consecutive_failures:
                chosen = self.rng.choice(remaining, count, replace=False)
            else:
                chosen = remaining[np.argsort(margin[remaining])[-count:]]
            self.selected = self.protected.copy()
            self.selected[chosen] = True
            self.previous, self.last = self.coefficient.copy(), None
            self.stage_deadline = min(self.deadline, time.monotonic()+self.stage_seconds)
            promoted = False
            try:
                result = opt.minimize(self.objective, self.parameters, jac=True,
                    method="L-BFGS-B",
                    bounds=[(-70, 70)]*(self.units*self.n)+[(-35, 35)]*self.units,
                    options={"maxiter": 100000, "maxfun": 100000, "maxcor": 50,
                             "maxls": 40, "gtol": 1e-10, "ftol": 1e-15})
                termination = str(result.message)
            except StageComplete:
                termination = "exact full-cube certificate" if self.certificate else "numerical stage passed"
                self.parameters, self.coefficient, margin = self.last
                # Previously protected points are explicitly retained.
                self.protected = self.selected | (margin > 1e-4)
                self.save("protected-checkpoint.npz", self.parameters, self.coefficient)
                np.save(self.out/"protected-mask.npy", self.protected)
                promoted = True
            except BudgetExpired:
                termination = "stage budget, total budget, or stop file"
            record = {"stage": len(self.stages), "termination": termination,
                      "protected_vertices": int(self.protected.sum()),
                      "introduced_vertices": chosen.tolist(), "batch": self.batch,
                      "promoted": promoted, "seconds": time.monotonic()-self.start}
            self.stages.append(record)
            print(json.dumps({"stage_summary": record}), flush=True)
            if self.certificate:
                break
            if promoted:
                consecutive_failures = 0
                self.batch = min(64, max(self.batch, 2*count))
            else:
                consecutive_failures += 1
                self.batch = max(1, self.batch//2)
        result = {"n": self.n, "lifted_heads": self.units+1,
                  "original_protected_vertices": self.original_protected,
                  "last_protected_vertices": int(self.protected.sum()),
                  "best_full_metric": self.best, "certificate": self.certificate,
                  "seconds": time.monotonic()-self.start,
                  "stages": self.stages, "events": self.events,
                  "scope": "Finite numerical continuation only. Stage tests are not exact proofs.",
                  "failure_is_not_a_lower_bound": True}
        (self.out/"result.json").write_text(json.dumps(result)+"\n")
        print(json.dumps({k: v for k, v in result.items() if k not in ("stages", "events")}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--stage-seconds", type=float, default=1800)
    parser.add_argument("--batch", type=int, default=8)
    parser.add_argument("--seed", type=int, default=2026112202)
    args = parser.parse_args()
    assert args.batch > 0 and args.stage_seconds > 0 and args.seconds > 0
    args.out.mkdir(parents=True, exist_ok=True)
    Curriculum(args.checkpoint, args.out, args.seconds, args.stage_seconds,
               args.batch, args.seed).run()
