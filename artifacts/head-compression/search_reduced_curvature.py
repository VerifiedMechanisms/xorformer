#!/usr/bin/env python3
"""Finite denominator search with the exact reduced squared-hinge Hessian.

At a smooth, nondegenerate inner optimum, eliminating the affine numerator
coordinates gives a Schur complement. Both residual curvature terms are
retained here. This is a numerical experiment, not a convergence theorem.
Run substantial instances through heavy. Success requires exact export checks.
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


def evaluate(t, labels, logs, previous=None, solver="newton", initial_score=None):
    count, heads, n = t.shape
    slopes = np.exp(logs)
    denominator = 1+np.einsum("xhi,hi->xh", t, slopes)
    local = t/denominator[:, :, None]
    features = np.column_stack((np.ones(count), local.reshape(count, -1)))
    q, triangular = la.qr(features, mode="economic", check_finite=False)
    initial = (q.T@initial_score if initial_score is not None else
               q.T@(features@previous) if previous is not None else q.T@labels)
    fit = convex_hinge_fit(labels[:, None]*q, initial, solver, 0.)
    coefficient = la.solve_triangular(triangular, fit.x, check_finite=False)
    score = q@fit.x
    residual = np.maximum(1-labels*score, 0)
    return dict(loss=float(residual@residual/(2*count)), coefficient=coefficient,
                q=q, triangular=triangular, local=local, score=score,
                residual=residual, inner_gradient=float(np.max(np.abs(fit.jac))))


def reduced_hessian(state, labels, logs, return_lift=False):
    local, coefficient = state["local"], state["coefficient"]
    count, heads, n = local.shape
    q = state["q"]
    active = state["residual"] > 0
    weight = labels*state["residual"]
    probabilities = local*np.exp(logs)[None, :, :]
    head_scores = np.einsum("xhi,hi->xh", local, coefficient[1:].reshape(heads, n))
    jacobian = (-head_scores[:, :, None]*probabilities).reshape(count, -1)
    gradient = -jacobian.T@weight/count
    aa = q[active].T@q[active]
    raw_mixed = np.zeros((1+heads*n, heads*n))
    bb = jacobian[active].T@jacobian[active]/count
    for h in range(heads):
        sl = slice(h*n, (h+1)*n)
        p = probabilities[:, h]
        # Minus the residual-weighted numerator/log-denominator mixed
        # derivative. The bias row vanishes.
        raw_mixed[1+h*n:1+(h+1)*n, sl] = (
            local[:, h].T@(weight[:, None]*p)/count)
        weighted_score = weight*head_scores[:, h]
        bb[sl, sl] -= (2*p.T@(weighted_score[:, None]*p)
                       -np.diag(p.T@weighted_score))/count
    transformed_mixed = la.solve_triangular(
        state["triangular"].T, raw_mixed, lower=True, check_finite=False)
    ab = (q[active].T@jacobian[active]/np.sqrt(count)
          +np.sqrt(count)*transformed_mixed)
    # The formula is exact only when the inner Gram matrix is nonsingular.
    # The explicitly reported regularizer is a numerical safeguard.
    regularizer = 1e-12
    aa.flat[::len(aa)+1] += regularizer
    solved = la.solve(aa, ab, assume_a="pos", check_finite=False)
    reduced = bb-ab.T@solved
    reduced = (reduced+reduced.T)/2
    scale = np.sqrt(np.maximum(np.mean(jacobian[active]**2, axis=0), 1e-20))
    normalized = reduced/scale[:, None]/scale[None, :]
    answer = (gradient/scale, normalized, scale, regularizer)
    if return_lift:
        lift = -np.sqrt(count)*la.solve_triangular(
            state["triangular"], solved, check_finite=False)
        return (*answer, lift)
    return answer


def run(checkpoint, out, seconds, max_iterations=10000):
    saved = np.load(checkpoint)
    labels = saved["labels"].astype(float)
    orientation = saved["orientation"].astype(int)
    logs = saved["logs"].copy()
    heads, n = logs.shape
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    start = time.monotonic()
    deadline = start+seconds
    coefficient = saved["coefficients"]
    events = []
    certificate = None
    state = evaluate(t, labels, logs, coefficient)
    for iteration in range(max_iterations):
        if time.monotonic() >= deadline:
            break
        margin = labels*state["score"]
        np.savez(out/"checkpoint.npz", labels=labels, orientation=orientation,
                 logs=logs, coefficients=state["coefficient"])
        event = dict(iteration=iteration, seconds=time.monotonic()-start,
                     loss=state["loss"], errors=int((margin <= 0).sum()),
                     minimum_margin=float(margin.min()),
                     inner_gradient=state["inner_gradient"])
        if margin.min() > 1e-5:
            cert = export(n, labels, state["coefficient"][1:].reshape(heads, n),
                          np.exp(logs), orientation, state["coefficient"][0])
            check = exact_check(cert)
            if check["certified"]:
                cert["verification"] = check
                (out/"certificate.json").write_text(json.dumps(cert)+"\n")
                certificate = "certificate.json"
                events.append(event)
                break
        gradient, hessian, scale, regularizer = reduced_hessian(state, labels, logs)
        eig, vectors = la.eigh(hessian, subset_by_index=[0, 0], check_finite=False)
        event.update(minimum_eigenvalue=float(eig[0]),
                     reduced_gradient_norm=float(la.norm(gradient)),
                     inner_gram_regularizer=regularizer)
        directions = []
        for relative in (1.01, 2., 10.):
            damping = max(1e-5, -float(eig[0])*relative+1e-6)
            shifted = hessian.copy()
            shifted.flat[::len(shifted)+1] += damping
            d = la.solve(shifted, -gradient, assume_a="pos", check_finite=False)/scale
            directions.append((f"newton-{relative}", d))
        if eig[0] < -1e-8:
            directions.extend((f"negative-{s}", s*vectors[:, 0]/scale)
                              for s in (-1, 1))
        best = None
        trials = 0
        for name, d in directions:
            d = d.reshape(heads, n)
            d *= min(1., 1/max(float(np.max(np.abs(d))), 1e-30))
            for backtrack in range(12):
                if time.monotonic() >= deadline:
                    break
                alpha = 2.**(-backtrack)
                trial_logs = np.clip(logs+alpha*d, -35, 35)
                trial = evaluate(t, labels, trial_logs, state["coefficient"])
                trials += 1
                if trial["loss"] < state["loss"]-max(1e-13, 1e-9*state["loss"]):
                    if best is None or trial["loss"] < best[0]["loss"]:
                        best = (trial, trial_logs, name, alpha)
                    break
        event["trial_evaluations"] = trials
        event["accepted_direction"] = None if best is None else best[2]
        event["step"] = None if best is None else best[3]
        events.append(event)
        print(json.dumps(event), flush=True)
        if best is None:
            break
        state, logs = best[:2]
    np.savez(out/"checkpoint.npz", labels=labels, orientation=orientation,
             logs=logs, coefficients=state["coefficient"])
    result = dict(n=n, heads=heads, seconds=time.monotonic()-start, events=events,
                  final_loss=state["loss"], certificate=certificate,
                  scope="One finite truth table; no universal or convergence theorem.",
                  failure_is_not_a_lower_bound=True)
    (out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--iterations", type=int, default=10000)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.seconds, args.iterations)
