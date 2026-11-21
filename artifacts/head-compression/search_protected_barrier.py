#!/usr/bin/env python3
"""Maintain numerical protected signs during joint rational-head continuation.

The loss is a squared hinge on one new vertex, a logarithmic barrier on
protected vertices, and a small score-space quadratic regularizer. Damped
Gauss--Newton steps move numerators and denominators together. Every accepted
step is tested on the actual score and must retain the protected signs.
Only a separately verified full-cube rational certificate counts as success.
No global convergence or universal head bound is asserted. Use heavy.
"""
import argparse
import json
import os
from pathlib import Path
import time

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import numpy as np
import scipy.linalg as la
import scipy.sparse.linalg as spla
from search_shared_affine_varpro import exact_lift, features, initialize, unpack
from search_shared_affine_gauss_newton import quick_score, score_jacobian


def barrier_terms(labels, score, protected, target, mu, ridge):
    margin = labels*score
    if np.min(margin[protected]) <= 0:
        return float("inf"), None, None
    count = int(protected.sum())
    value = ridge*float(score@score)/(2*len(score))
    gradient = ridge*score/len(score)
    curvature = np.full(len(score), ridge/len(score))
    value -= mu*float(np.log(margin[protected]).sum())/count
    gradient[protected] -= mu*labels[protected]/(count*margin[protected])
    curvature[protected] += mu/(count*margin[protected]**2)
    residual = max(1-margin[target], 0.)
    value += residual*residual/2
    gradient[target] -= labels[target]*residual
    curvature[target] += float(residual > 0)
    return float(value), gradient, curvature


def precise_score(x, logs, separation, coefficient):
    """Extended-precision diagnostic, not an interval certificate."""
    dtype = np.longdouble
    xx, cc = x.astype(dtype), coefficient.astype(dtype)
    # Match the rounded shifts used by the exact-lift exporter.
    pp = np.exp((logs-logs.max(axis=1, keepdims=True)).astype(dtype))
    qq = np.exp(2*separation.astype(dtype))
    t1, t0 = xx@pp.T, (1-xx)@pp.T
    rr = (qq/(qq+1))*(t1-t0)/(qq*t1+t0)
    n = x.shape[1]
    aa = cc[n+1:].reshape(logs.shape)
    return cc[0]+xx@cc[1:n+1]+((xx@aa.T)*rr).sum(axis=1)


def direction(x, parameters, coefficient, units, gradient, curvature,
              damping, maxiter):
    logs, separation = unpack(parameters, units, x.shape[1])
    feature = features(x, logs, separation)
    q, r = la.qr(feature, mode="economic", check_finite=False)
    del feature
    jac = score_jacobian(x, logs, separation, coefficient)
    sqrt_w = np.sqrt(curvature)
    scale_q = np.sqrt(np.einsum("ij,i,ij->j", q, curvature, q))
    scale_j = np.sqrt(np.einsum("ij,i,ij->j", jac, curvature, jac))
    floor_q = max(float(np.median(scale_q))*1e-5, 1e-15)
    floor_j = max(float(np.median(scale_j))*1e-5, 1e-15)
    scale_q, scale_j = np.maximum(scale_q, floor_q), np.maximum(scale_j, floor_j)
    q /= scale_q
    jac /= scale_j
    width = q.shape[1]
    def forward(z):
        return sqrt_w*(q@z[:width]+jac@z[width:])
    def backward(v):
        wv = sqrt_w*v
        return np.r_[q.T@wv, jac.T@wv]
    operator = spla.LinearOperator((len(x), width+jac.shape[1]),
        matvec=forward, rmatvec=backward, dtype=float)
    fit = spla.lsmr(operator, -gradient/sqrt_w, damp=np.sqrt(damping),
                    atol=1e-7, btol=1e-7, maxiter=maxiter)
    linear_change = (operator@fit[0])/sqrt_w
    derivative = float(gradient@linear_change)
    kind = "joint barrier Gauss-Newton"
    if not np.isfinite(derivative) or derivative >= 0:
        vector = -backward(gradient/sqrt_w)
        linear_change = (operator@vector)/sqrt_w
        derivative = float(gradient@linear_change)
        kind = "scaled joint gradient"
    else:
        vector = fit[0]
    response = la.solve_triangular(r, vector[:width]/scale_q, check_finite=False)
    nonlinear = vector[width:]/scale_j
    diagnostic = {"direction": kind, "model_derivative": derivative,
                  "lsmr_stop": int(fit[1]), "lsmr_iterations": int(fit[2]),
                  "lsmr_residual_norm": float(fit[3]),
                  "lsmr_normal_residual_norm": float(fit[4])}
    return nonlinear, response, diagnostic


def backtrack(x, labels, parameters, coefficient, units, protected, target,
              mu, ridge, nonlinear, response, max_step, deadline, stop_path):
    initial_score = quick_score(x, *unpack(parameters, units, x.shape[1]), coefficient)
    initial_value = barrier_terms(labels, initial_score, protected, target, mu, ridge)[0]
    scale = min(1., max_step/max(float(np.max(np.abs(nonlinear))), 1e-30))
    nonlinear, response = scale*nonlinear, scale*response
    bounds = np.r_[np.full(units*x.shape[1], 70.), np.full(units, 35.)]
    nonlinear = np.clip(parameters+nonlinear, -bounds, bounds)-parameters
    for power in range(40):
        if time.monotonic() >= deadline or stop_path.exists():
            return None
        alpha = 2.**(-power)
        trial_p, trial_c = parameters+alpha*nonlinear, coefficient+alpha*response
        logs, separation = unpack(trial_p, units, x.shape[1])
        score = quick_score(x, logs, separation, trial_c)
        if np.min((labels*score)[protected]) <= 1e-7:
            continue
        value = barrier_terms(labels, score, protected, target, mu, ridge)[0]
        if np.isfinite(value) and value < initial_value-max(1e-12, abs(initial_value)*1e-10):
            precise = precise_score(x, logs, separation, trial_c)
            if np.min((labels*precise)[protected]) <= 1e-7:
                continue
            precise_initial = precise_score(x, *unpack(parameters, units, x.shape[1]), coefficient)
            precise_old_value = barrier_terms(labels, precise_initial, protected, target, mu, ridge)[0]
            precise_value = barrier_terms(labels, precise, protected, target, mu, ridge)[0]
            if precise_value >= precise_old_value-max(1e-12, abs(precise_old_value)*1e-10):
                continue
            return trial_p, trial_c, score, {
                "alpha": alpha, "direction_scale": scale, "value_after": value,
                "extended_value_after": precise_value,
                "extended_minimum_protected_margin": float(np.min((labels*precise)[protected])),
                "double_extended_score_discrepancy": float(np.max(np.abs(score-precise)))}
    return None


def run(checkpoint, out, seconds, mu, ridge, damping, maxiter, max_step, seed):
    labels, logs, separation, coefficient = initialize(checkpoint)
    units, n = logs.shape
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    parameters = np.r_[logs.ravel(), separation]
    start, rng = time.monotonic(), np.random.default_rng(seed)
    deadline, stop_path = start+seconds, out/"STOP"
    score = quick_score(x, logs, separation, coefficient)
    protected = labels*score > 1e-3
    assert protected.any() and np.isfinite(score).all()
    events, best, certificate = [], None, None
    target, failed_steps, target_steps = None, 0, 0
    def save(name):
        ll, ss = unpack(parameters, units, n)
        np.savez(out/name, labels=labels, logs=ll, separation=ss,
                 coefficients=coefficient, kind="shared-affine")
    save("initial.npz")
    while time.monotonic() < deadline and not stop_path.exists():
        margin = labels*score
        precise = precise_score(x, *unpack(parameters, units, n), coefficient)
        precise_margin = labels*precise
        if margin.min() > 1e-4 and precise_margin.min() > 1e-4:
            cert, check = exact_lift(labels, *unpack(parameters, units, n), coefficient)
            if cert is not None:
                (out/"certificate.json").write_text(json.dumps(cert)+"\n")
                certificate = "certificate.json"
                break
        promote = (margin > 1e-3) & (precise_margin > 1e-3)
        protected |= promote
        if protected.all():
            # Do not report a numerical sign test as a certificate.
            break
        assert min(margin[protected].min(), precise_margin[protected].min()) > 0
        remaining = np.flatnonzero(~protected)
        if target is None or protected[target] or target_steps >= 25 or failed_steps >= 3:
            if target is None or protected[target]:
                target = int(remaining[np.argmax(margin[remaining])])
            else:
                target = int(rng.choice(remaining))
            target_steps, failed_steps = 0, 0
        value, gradient, curvature = barrier_terms(labels, score, protected, target, mu, ridge)
        event = {"iteration": len(events), "seconds": time.monotonic()-start,
                 "protected_vertices": int(protected.sum()), "errors": int((margin <= 0).sum()),
                 "target": target, "target_margin": float(margin[target]),
                 "minimum_protected_margin": float(margin[protected].min()),
                 "minimum_margin": float(margin.min()), "value": value,
                 "mu": mu, "ridge": ridge, "damping": damping}
        print(json.dumps({"phase": "start", **event}), flush=True)
        nonlinear, response, diagnostic = direction(x, parameters, coefficient, units,
            gradient, curvature, damping, maxiter)
        event.update(diagnostic)
        trial = backtrack(x, labels, parameters, coefficient, units, protected, target,
            mu, ridge, nonlinear, response, max_step, deadline, stop_path)
        target_steps += 1
        if trial is None:
            damping = min(1e6, damping*10)
            failed_steps += 1
            event["accepted"] = False
        else:
            parameters, coefficient, score, detail = trial
            event.update(detail)
            event["accepted"] = True
            damping = max(1e-8, damping*.8)
            failed_steps = 0
            save("latest.npz")
            metric = int((labels*score <= 0).sum()), -float((labels*score).min())
            if best is None or metric < best:
                best = metric
                save("checkpoint.npz")
                np.save(out/"protected-mask.npy", protected)
        event["completed_seconds"] = time.monotonic()-start
        events.append(event)
        print(json.dumps({"phase": "complete", **event}), flush=True)
    result = {"n": n, "lifted_heads": units+1, "seconds": time.monotonic()-start,
              "protected_vertices": int(protected.sum()), "best_metric": best,
              "certificate": certificate, "events": events,
              "scope": "Finite heuristic with numerical protected signs. No universal theorem.",
              "failure_is_not_a_lower_bound": True}
    (out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


def self_test(out):
    rng = np.random.default_rng(2026112204)
    n, units = 5, 2
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    logs, separation = rng.normal(size=(units, n)), np.array([.7, -.6])
    coefficient = rng.normal(size=n+1+n*units)
    parameters = np.r_[logs.ravel(), separation]
    score = quick_score(x, logs, separation, coefficient)
    labels = np.where(score > 0, 1., -1.)
    target = int(np.argmin(np.abs(score)))
    labels[target] *= -1
    protected = np.arange(len(x)) != target
    mu, ridge = .1, 1e-6
    value, gradient, curvature = barrier_terms(labels, score, protected, target, mu, ridge)
    eps = 1e-6
    errors, herrors = [], []
    for j in range(len(x)):
        step = np.zeros(len(x)); step[j] = eps
        fp, gp, _ = barrier_terms(labels, score+step, protected, target, mu, ridge)
        fm, gm, _ = barrier_terms(labels, score-step, protected, target, mu, ridge)
        errors.append(abs((fp-fm)/(2*eps)-gradient[j]))
        herrors.append(abs((gp[j]-gm[j])/(2*eps)-curvature[j]))
    assert max(errors) < 1e-6 and max(herrors) < 1e-5
    nonlinear, response, diagnostic = direction(x, parameters, coefficient, units,
        gradient, curvature, 1e-3, 150)
    trial = backtrack(x, labels, parameters, coefficient, units, protected, target,
        mu, ridge, nonlinear, response, .5, time.monotonic()+30, out/"STOP")
    assert trial is not None and diagnostic["model_derivative"] < 0
    result = {"n": n, "units": units, "gradient_error": max(errors),
              "curvature_error": max(herrors), "initial_value": value,
              "initial_target_margin": float(labels[target]*score[target]),
              "final_target_margin": float(labels[target]*trial[2][target]),
              **diagnostic, **trial[3],
              "scope": "Numerical derivative and protected-descent check only."}
    (out/"self-test.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", nargs="?", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--mu", type=float, default=.1)
    parser.add_argument("--ridge", type=float, default=1e-6)
    parser.add_argument("--damping", type=float, default=.001)
    parser.add_argument("--maxiter", type=int, default=150)
    parser.add_argument("--max-step", type=float, default=.5)
    parser.add_argument("--seed", type=int, default=2026112204)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    assert min(args.mu, args.ridge, args.damping, args.max_step, args.seconds) > 0
    args.out.mkdir(parents=True, exist_ok=True)
    if args.self_test:
        self_test(args.out)
    else:
        assert args.checkpoint is not None
        run(args.checkpoint, args.out, args.seconds, args.mu, args.ridge,
            args.damping, args.maxiter, args.max_step, args.seed)
