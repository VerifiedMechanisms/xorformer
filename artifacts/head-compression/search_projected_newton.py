#!/usr/bin/env python3
"""Joint denominator search with the numerator tangent space eliminated.

This tests a different descent mechanism on saved finite instances. Numerical
descent, including apparent convergence, is never used as a proof. Every
reported success is exported to the independent integer certificate format.
Run through heavy.
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
from search_varpro_scores import convex_hinge_fit
from search_newton_scores import export
from search_sign_scores import exact_check


def run(checkpoint, out, seconds, seed):
    saved = np.load(checkpoint)
    y = saved["labels"].astype(float)
    orientation = saved["orientation"].astype(int)
    n, h = len(y).bit_length()-1, len(orientation)
    assert len(y) == 1 << n
    logs = saved["logs"].reshape(h, n).copy()
    x = ((np.arange(len(y))[:, None] >> np.arange(n)) & 1).astype(float)
    t = np.where(orientation[None, :, None] > 0,
                 x[:, None, :], 1-x[:, None, :])
    rng = np.random.default_rng(seed)
    start = time.monotonic()
    deadline = start+seconds
    best_loss = float("inf")
    best_logs = logs.copy()
    previous = None
    damping = 1e-3
    events = []
    evaluations = 0

    def evaluate(ll, previous):
        b = np.exp(ll)
        den = 1+np.einsum("xhi,hi->xh", t, b)
        features = np.column_stack((np.ones(len(y)),
                                    (t/den[:, :, None]).reshape(len(y), -1)))
        q, r = la.qr(features, mode="economic", check_finite=False)
        initial = q.T @ (features @ previous) if previous is not None else q.T @ y
        fit = convex_hinge_fit(y[:, None]*q, initial, "newton", 0.)
        coefficient = la.solve_triangular(r, fit.x, check_finite=False)
        score = q @ fit.x
        residual = np.maximum(1-y*score, 0)
        loss = .5*(residual @ residual)/len(y)
        return loss, coefficient, score, residual, q, den, b, fit

    certificate = None
    iteration = 0
    while time.monotonic() < deadline:
        loss, coeff, score, residual, q, den, b, fit = evaluate(logs, previous)
        previous = coeff
        evaluations += 1
        if loss < best_loss:
            best_loss, best_logs = loss, logs.copy()
            np.savez(out/"checkpoint.npz", logs=logs, coefficients=coeff,
                     orientation=orientation, labels=y)
        margin = y*score
        event = {"iteration": iteration, "evaluations": evaluations,
                 "seconds": time.monotonic()-start, "n": n, "heads": h,
                 "loss": float(loss), "errors": int((margin <= 0).sum()),
                 "minimum_margin": float(margin.min()), "damping": damping,
                 "inner_gradient": float(np.max(np.abs(fit.jac)))}
        events.append(event)
        print(json.dumps(event), flush=True)
        if margin.min() > 1e-6:
            cert = export(n, y, coeff[1:].reshape(h, n), b, orientation, coeff[0])
            check = exact_check(cert)
            if check["certified"]:
                cert["verification"] = check
                certificate = "certificate.json"
                (out/certificate).write_text(json.dumps(cert)+"\n")
                break

        active = residual > 0
        # The active residual is orthogonal to the numerator columns at an
        # exact inner optimum. Project out those columns before computing the
        # denominator correction. This is a Gauss-Newton approximation, not
        # an assertion that the reduced Hessian is positive definite.
        qa, _ = la.qr((y[:, None]*q)[active], mode="economic", check_finite=False)
        numerator = np.einsum("xhi,hi->xh", t, coeff[1:].reshape(h, n))
        jacobian = (-numerator[:, :, None]*t*b[None, :, :]/den[:, :, None]**2)
        ja = (y[:, None]*jacobian.reshape(len(y), -1))[active]
        projected = ja-qa @ (qa.T @ ja)
        scale = np.maximum(la.norm(projected, axis=0), 1e-20)
        normalized = projected/scale
        gram = normalized.T @ normalized
        gram.flat[::len(gram)+1] += damping
        rhs = normalized.T @ residual[active]
        # Remove outward directions at active box constraints. Clipping an
        # unconstrained Newton direction afterwards need not preserve descent.
        free = np.ones(len(rhs), dtype=bool)
        flat_logs = logs.ravel()
        for _ in range(len(rhs)+1):
            delta = np.zeros(len(rhs))
            if not free.any():
                break
            subgram = gram[np.ix_(free, free)]
            try:
                delta[free] = la.solve(subgram, rhs[free], assume_a="pos",
                                      check_finite=False)/scale[free]
            except la.LinAlgError:
                delta[free] = la.lstsq(subgram, rhs[free], check_finite=False)[0]/scale[free]
            outward = (((flat_logs >= 20-1e-8) & (delta > 0)) |
                       ((flat_logs <= -20+1e-8) & (delta < 0))) & free
            if not outward.any():
                break
            free[outward] = False
        delta = delta.reshape(h, n)
        alpha = min(1., 2/max(np.max(np.abs(delta)), 1e-30))
        moving = np.abs(delta) > 1e-30
        if moving.any():
            distance = np.where(delta > 0, 20-logs, -20-logs)
            alpha = min(alpha, float(np.min((distance[moving]/delta[moving]))))
        accepted = False
        for _ in range(20):
            if time.monotonic() >= deadline:
                break
            trial_logs = np.clip(logs+alpha*delta, -20, 20)
            trial = evaluate(trial_logs, coeff)
            evaluations += 1
            if trial[0] < loss-max(1e-14, loss*1e-8):
                logs, previous = trial_logs, trial[1]
                accepted = True
                break
            alpha *= .5
        if accepted:
            damping = max(damping*.7, 1e-8)
        else:
            damping = min(damping*10, 1e2)
            if damping >= 1e2:
                logs = np.clip(best_logs+rng.normal(0, .25, logs.shape), -20, 20)
                previous = None
                damping = 1e-3
        iteration += 1
    result = {"n": n, "heads": h, "seconds": time.monotonic()-start,
              "best_loss": float(best_loss), "certificate": certificate,
              "events": events, "failure_is_not_a_lower_bound": True}
    (out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("checkpoint", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=3600)
    p.add_argument("--seed", type=int, default=130000)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.seconds, args.seed)
