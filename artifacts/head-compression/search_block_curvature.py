#!/usr/bin/env python3
"""Finite score search using exact single-head squared-hinge curvature.

This experiment checks both Newton directions and negative-curvature directions.
Every accepted update passes a numerical finite-loss decrease check. Cached sums
are recomputed each sweep; floating-point checks are not exact certificates.
No global convergence or universal head bound is claimed. Run with heavy.
"""
import argparse
import json
import os
from pathlib import Path
import time

for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
from scipy.optimize import brentq
from search_newton_scores import export
from search_sign_scores import exact_check


def head_data(t, logs, values):
    b = np.exp(logs)
    p = t*b/(1+t@b)[:, None]
    return p@values, p


def derivatives(p, values, score, labels, value_scale):
    """Derivatives for parameters (delta values / scale, delta log slopes)."""
    q = p@values
    residual = np.maximum(1-labels*score, 0)
    active = residual > 0
    w = labels*residual
    jb = p*(values-q[:, None])
    j = np.column_stack((value_scale*p, jb))
    gradient = -j.T@w/len(labels)
    hessian = j[active].T@j[active]
    moment = p.T@(w[:, None]*p)
    z = p.T@w
    k = jb.T@w
    mixed = value_scale*(np.diag(z)-moment)
    bb = (np.diag(k)-(values[:, None]+values[None, :])*moment
          +2*p.T@((w*q)[:, None]*p))
    n = len(values)
    hessian[:n, n:] -= mixed
    hessian[n:, :n] -= mixed.T
    hessian[n:, n:] -= bb
    return gradient, hessian/len(labels)


def bias_refit(score, labels):
    derivative = lambda shift: -np.mean(
        labels*np.maximum(1-labels*(score+shift), 0))
    radius = max(1., float(np.max(np.abs(score)))+2)
    if derivative(-radius) == 0:
        return -radius
    if derivative(radius) == 0:
        return radius
    return brentq(derivative, -radius, radius, xtol=1e-12)


def run(checkpoint, out, seconds, seed):
    saved = np.load(checkpoint)
    labels = saved["labels"].astype(float)
    orientation = saved["orientation"].astype(int)
    n = len(labels).bit_length()-1
    h = len(orientation)
    logs = saved["logs"].reshape(h, n).copy()
    coefficient = saved["coefficients"]
    values = coefficient[1:].reshape(h, n)/np.exp(logs)
    bias = float(coefficient[0])
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    t = np.where(orientation[None, :, None] > 0,
                 x[:, None, :], 1-x[:, None, :])
    terms = np.column_stack([head_data(t[:, j], logs[j], values[j])[0]
                             for j in range(h)])
    score = bias+terms.sum(axis=1)
    rng = np.random.default_rng(seed)
    start = time.monotonic()
    deadline = start+seconds
    loss_of = lambda s: float(np.mean(np.maximum(1-labels*s, 0)**2)/2)
    loss = loss_of(score)
    sweep = 0
    events = []
    certificate = None
    trust = np.full(h, .5)
    while time.monotonic() < deadline:
        accepted = negative_used = negative_seen = 0
        for j in rng.permutation(h):
            if time.monotonic() >= deadline:
                break
            old_term, p = head_data(t[:, j], logs[j], values[j])
            # This is a fixed linear coordinate scale during the local step.
            scale = max(1., float(np.max(np.abs(values[j]))))
            gradient, hessian = derivatives(p, values[j], score, labels, scale)
            eigenvalues, eigenvectors = np.linalg.eigh(hessian)
            floor = max(1e-12, 1e-6*float(np.max(np.abs(eigenvalues))))
            direction = -eigenvectors@(
                (eigenvectors.T@gradient)/np.maximum(np.abs(eigenvalues), floor))
            direction *= min(1., trust[j]/max(np.max(np.abs(direction)), 1e-30))
            candidates = [("newton", direction)]
            if eigenvalues[0] < -10*floor:
                negative_seen += 1
                d = eigenvectors[:, 0]
                d = d*trust[j]/max(np.max(np.abs(d)), 1e-30)
                candidates.extend([("negative", d), ("negative", -d)])
            best = None
            for kind, direction in candidates:
                alpha = 1.
                for _ in range(10):
                    trial_v = values[j]+alpha*scale*direction[:n]
                    trial_l = np.clip(logs[j]+alpha*direction[n:], -35, 35)
                    trial_q, _ = head_data(t[:, j], trial_l, trial_v)
                    trial_s = score+(trial_q-old_term)
                    trial_loss = loss_of(trial_s)
                    if trial_loss < loss-max(1e-14, 1e-10*loss):
                        if best is None or trial_loss < best[0]:
                            best = (trial_loss, trial_v, trial_l, trial_q,
                                    trial_s, kind, alpha)
                        break
                    alpha *= .5
            if best is not None:
                loss, values[j], logs[j], terms[:, j], score, kind, alpha = best
                accepted += 1
                negative_used += kind == "negative"
                trust[j] = min(2., trust[j]*(1.2 if alpha >= .5 else .8))
            else:
                trust[j] = max(.01, trust[j]*.5)
        shift = bias_refit(score, labels)
        bias += shift
        # Recompute to avoid accumulated subtraction error in cached scores.
        terms = np.column_stack([head_data(t[:, j], logs[j], values[j])[0]
                                 for j in range(h)])
        score = bias+terms.sum(axis=1)
        loss = loss_of(score)
        margin = labels*score
        coeff = np.r_[bias, (values*np.exp(logs)).ravel()]
        np.savez(out/"checkpoint.npz", labels=labels, orientation=orientation,
                 logs=logs, coefficients=coeff)
        event = {"sweep": sweep, "seconds": time.monotonic()-start,
                 "loss": loss, "errors": int((margin <= 0).sum()),
                 "minimum_margin": float(margin.min()), "accepted": accepted,
                 "negative_curvature_seen": negative_seen,
                 "negative_curvature_used": negative_used}
        events.append(event)
        print(json.dumps(event), flush=True)
        if margin.min() > 1e-5:
            cert = export(n, labels, coeff[1:].reshape(h, n), np.exp(logs),
                          orientation, bias)
            check = exact_check(cert)
            if check["certified"]:
                cert["verification"] = check
                (out/"certificate.json").write_text(json.dumps(cert)+"\n")
                certificate = "certificate.json"
                break
        sweep += 1
    result = {"n": n, "heads": h, "seconds": time.monotonic()-start,
              "certificate": certificate, "events": events,
              "scope": "One finite truth table only. No global convergence theorem.",
              "failure_is_not_a_lower_bound": True}
    (out/"result.json").write_text(json.dumps(result)+"\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--seed", type=int, default=460000)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.seconds, args.seed)
