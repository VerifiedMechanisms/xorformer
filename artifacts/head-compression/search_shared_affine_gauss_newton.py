#!/usr/bin/env python3
"""Joint damped Gauss--Newton steps in the shared-affine chart.

The linear coefficient response is represented in QR coordinates. The
nonlinear direction and that response are tested together on the actual
score before refitting. This is a finite heuristic, not a convergence or
capacity theorem. Run substantial computations through heavy.
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
from search_shared_affine_varpro import (
    exact_lift, features, geometry, initialize, score_gradient, unpack,
)
from search_varpro_scores import convex_hinge_fit


def quick_score(x, logs, separation, coefficient):
    n = x.shape[1]
    a = coefficient[n+1:].reshape(logs.shape)
    r = geometry(x, logs, separation)[-1]
    return coefficient[0]+x@coefficient[1:n+1]+((x@a.T)*r).sum(axis=1)


def loss_value(labels, score):
    error = np.maximum(1-labels*score, 0.)
    return float(error@error/(2*len(labels)))


def score_jacobian(x, logs, separation, coefficient):
    """Derivative with respect to the flattened logs and separations."""
    units, n = logs.shape
    p, q, t1, t0, b, r = geometry(x, logs, separation)
    a = coefficient[n+1:].reshape(units, n)
    ax = x@a.T
    jac = np.empty((len(x), units*(n+1)))
    for h in range(units):
        z = ax[:, h]*q[h]/b[:, h]**2
        jac[:, h*n:(h+1)*n] = (
            z[:, None]*(x*(t1[:, h]+t0[:, h])[:, None]-t1[:, h, None])
            *p[h])
    jac[:, units*n:] = ax*r*(2/(q+1)-2*q*t1/b)
    return jac


def evaluate(x, labels, parameters, units, previous):
    logs, separation = unpack(parameters, units, x.shape[1])
    feature = features(x, logs, separation)
    q, r = la.qr(feature, mode="economic", check_finite=False)
    initial = q.T@(feature@previous) if previous is not None else q.T@labels
    del feature
    fit = convex_hinge_fit(labels[:, None]*q, initial, "newton", 0.)
    coefficient = la.solve_triangular(r, fit.x, check_finite=False)
    score = quick_score(x, logs, separation, coefficient)
    return {"q": q, "r": r, "coefficient": coefficient, "score": score,
            "loss": loss_value(labels, score),
            "inner_gradient": float(np.max(np.abs(fit.jac))),
            "direct_qr_score_discrepancy": float(np.max(np.abs(score-q@fit.x)))}


def joint_operator(q, jac, active):
    """Columns of jac are already normalized. Never mutate either input."""
    p, k = q.shape[1], jac.shape[1]
    def forward(z):
        return active*(q@z[:p]+jac@z[p:])
    def backward(y):
        yy = active*y
        return np.r_[q.T@yy, jac.T@yy]
    return spla.LinearOperator((len(q), p+k), matvec=forward,
                               rmatvec=backward, dtype=float)


def joint_direction(x, labels, parameters, units, state, damping, maxiter):
    logs, separation = unpack(parameters, units, x.shape[1])
    jac = score_jacobian(x, logs, separation, state["coefficient"])
    active = (labels*state["score"] < 1).astype(float)
    error = active*(state["score"]-labels)
    scales = np.sqrt(np.einsum("ij,i,ij->j", jac, active, jac))
    floor = max(float(np.median(scales))*1e-5, 1e-12)
    scales = np.maximum(scales, floor)
    jac /= scales
    operator = joint_operator(state["q"], jac, active)
    result = spla.lsmr(operator, -error, damp=np.sqrt(damping),
                      atol=1e-7, btol=1e-7, maxiter=maxiter)
    p = state["q"].shape[1]
    response = la.solve_triangular(state["r"], result[0][:p], check_finite=False)
    direction = result[0][p:]/scales
    change = operator@result[0]
    diagnostic = {"lsmr_stop": int(result[1]), "lsmr_iterations": int(result[2]),
                  "lsmr_residual_norm": float(result[3]),
                  "lsmr_normal_residual_norm": float(result[4]),
                  "linear_model_directional_derivative": float(error@change/len(labels)),
                  "linear_model_loss": float(la.norm(error+change)**2/(2*len(labels))),
                  "active_vertices": int(active.sum()), "scale_floor": floor}
    return direction, response, diagnostic


def backtrack(x, labels, parameters, state, direction, response, units,
              max_step, deadline, stop_path):
    size = max(float(np.max(np.abs(direction))), 1e-30)
    factor = min(1., max_step/size)
    direction, response = factor*direction, factor*response
    n = x.shape[1]
    # Clipping is included in the direction actually evaluated. The model
    # diagnostic is not claimed to remain exact after clipping.
    bounds = np.r_[np.full(units*n, 70.), np.full(units, 35.)]
    direction = np.clip(parameters+direction, -bounds, bounds)-parameters
    required = max(1e-13, 1e-9*state["loss"])
    for power in range(35):
        if time.monotonic() >= deadline or stop_path.exists():
            return None
        alpha = 2.**(-power)
        trial = parameters+alpha*direction
        coefficient = state["coefficient"]+alpha*response
        score = quick_score(x, *unpack(trial, units, n), coefficient)
        loss = loss_value(labels, score)
        if np.isfinite(loss) and loss < state["loss"]-required:
            return trial, coefficient, loss, alpha, factor
    return None


def run(checkpoint, out, seconds, damping, maxiter, max_step):
    labels, logs, separation, coefficient = initialize(checkpoint)
    labels = labels.astype(float)
    units, n = logs.shape
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    parameters = np.r_[logs.ravel(), separation]
    started = time.monotonic()
    deadline = started+seconds
    state = evaluate(x, labels, parameters, units, coefficient)
    events, certificate, termination = [], None, "budget or stop file"
    while time.monotonic() < deadline and not (out/"STOP").exists():
        logs, separation = unpack(parameters, units, n)
        np.savez(out/"checkpoint.npz", labels=labels, logs=logs,
                 separation=separation, coefficients=state["coefficient"],
                 kind="shared-affine")
        margin = labels*state["score"]
        event = {"iteration": len(events), "seconds": time.monotonic()-started,
                 "loss": state["loss"], "errors": int((margin <= 0).sum()),
                 "minimum_margin": float(margin.min()),
                 "inner_gradient": state["inner_gradient"],
                 "direct_qr_score_discrepancy": state["direct_qr_score_discrepancy"],
                 "damping": damping}
        print(json.dumps({"phase": "start", **event}), flush=True)
        if margin.min() > 1e-5:
            cert, check = exact_lift(labels, logs, separation, state["coefficient"])
            event["exact_check"] = check
            if cert is not None:
                (out/"certificate.json").write_text(json.dumps(cert)+"\n")
                certificate, termination = "certificate.json", "certificate"
                events.append(event)
                break
        direction, response, diagnostic = joint_direction(
            x, labels, parameters, units, state, damping, maxiter)
        event.update(diagnostic)
        trial = backtrack(x, labels, parameters, state, direction, response,
                          units, max_step, deadline, out/"STOP")
        event["direction"] = "joint Gauss-Newton"
        if trial is None and time.monotonic() < deadline and not (out/"STOP").exists():
            gradient = score_gradient(x, labels, logs, separation, state["coefficient"])[2]
            trial = backtrack(x, labels, parameters, state, -gradient,
                              np.zeros_like(response), units, max_step, deadline, out/"STOP")
            event["direction"] = "gradient fallback"
        if trial is None:
            termination = ("budget or stop file" if time.monotonic() >= deadline
                           or (out/"STOP").exists() else "no tested descent")
            events.append(event)
            break
        event.update(trial_loss=trial[2], alpha=trial[3], direction_scale=trial[4])
        print(json.dumps({"phase": "refit", **event}), flush=True)
        new = evaluate(x, labels, trial[0], units, trial[1])
        event["refitted_loss"] = new["loss"]
        event["refit_exceeds_trial"] = new["loss"] > trial[2]+1e-8
        event["completed_seconds"] = time.monotonic()-started
        events.append(event)
        print(json.dumps({"phase": "complete", **event}), flush=True)
        if not np.isfinite(new["loss"]) or new["loss"] >= state["loss"]-1e-13:
            termination = "refit failed to retain descent"
            break
        parameters, state = trial[0], new
        damping = max(1e-7, damping*.7) if trial[3] >= .5 else min(1., damping*2)
    logs, separation = unpack(parameters, units, n)
    np.savez(out/"checkpoint.npz", labels=labels, logs=logs,
             separation=separation, coefficients=state["coefficient"], kind="shared-affine")
    result = {"n": n, "units": units, "lifted_heads": units+1,
              "seconds": time.monotonic()-started, "termination": termination,
              "final_loss": state["loss"], "certificate": certificate, "events": events,
              "scope": "Finite numerical experiment; no universal or convergence theorem.",
              "failure_is_not_a_lower_bound": True}
    (out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


def self_test(out):
    rng = np.random.default_rng(2026112204)
    n, units = 5, 2
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    logs, coefficient = rng.normal(size=(units, n)), rng.normal(size=n+1+units*n)
    records = []
    for separation in (np.array([.6, -.8]), np.zeros(units)):
        parameters = np.r_[logs.ravel(), separation]
        jac = score_jacobian(x, logs, separation, coefficient)
        numeric = np.empty_like(jac)
        for i in range(len(parameters)):
            delta = np.zeros(len(parameters)); delta[i] = 1e-5
            numeric[:, i] = (quick_score(x, *unpack(parameters+delta, units, n), coefficient)
                             -quick_score(x, *unpack(parameters-delta, units, n), coefficient))/2e-5
        err = float(np.max(np.abs(jac-numeric)))
        assert err < 1e-8, err
        records.append({"separation": separation.tolist(), "jacobian_error": err})
    # Five-bit parity cannot have three heads, so this diagnostic cannot
    # accidentally start at a zero-loss fixed-feature fit.
    labels = 1.-2.*(x.sum(axis=1) % 2)
    separation = np.array([.6, -.8])
    parameters = np.r_[logs.ravel(), separation]
    state = evaluate(x, labels, parameters, units, None)
    assert state["loss"] > 1e-5, state["loss"]
    jac = score_jacobian(x, logs, separation, state["coefficient"])
    active = (labels*state["score"] < 1).astype(float)
    error = active*(state["score"]-labels)
    gradient = score_gradient(x, labels, logs, separation, state["coefficient"])[2]
    grad_error = float(np.max(np.abs(jac.T@error/len(x)-gradient)))
    assert grad_error < 1e-9, grad_error
    operator = joint_operator(state["q"], jac, active)
    u, v = rng.normal(size=operator.shape[1]), rng.normal(size=operator.shape[0])
    adjoint_error = abs(float((operator@u)@v-u@(operator.T@v)))
    assert adjoint_error < 1e-9, adjoint_error
    direction, response, diagnostic = joint_direction(
        x, labels, parameters, units, state, 1e-3, 200)
    assert diagnostic["linear_model_directional_derivative"] < -1e-9, diagnostic
    trial = backtrack(x, labels, parameters, state, direction, response,
                      units, 1., time.monotonic()+60, out/"STOP")
    assert trial is not None
    new = evaluate(x, labels, trial[0], units, trial[1])
    assert new["loss"] < state["loss"] and new["loss"] <= trial[2]+1e-8
    result = {"jacobians": records, "gradient_error": grad_error,
              "adjoint_error": adjoint_error, "old_loss": state["loss"],
              "trial_loss": trial[2], "refitted_loss": new["loss"],
              "alpha": trial[3], "joint_step": diagnostic,
              "scope": "Derivative and descent diagnostic only; no sign certificate."}
    (out/"self-test.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path, nargs="?")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--damping", type=float, default=1e-3)
    parser.add_argument("--maxiter", type=int, default=150)
    parser.add_argument("--max-step", type=float, default=1.)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.self_test:
        self_test(args.out)
    else:
        parser.error("checkpoint is required") if args.checkpoint is None else None
        run(args.checkpoint, args.out, args.seconds, args.damping, args.maxiter, args.max_step)
