#!/usr/bin/env python3
"""Coupled rational-score steps using the numerator response to denominators.

The Schur-complement direction is tested on the actual score with the first
order numerator response, before a costly full numerator refit. This is a
finite numerical search, with no global convergence claim. Use heavy.
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
from search_reduced_curvature import evaluate, reduced_hessian
from search_newton_scores import export
from search_sign_scores import exact_check


def quick_evaluate(t, labels, logs, coefficient):
    denominator = 1+np.einsum("xhi,hi->xh", t, np.exp(logs))
    numerator = np.einsum("xhi,hi->xh", t, coefficient[1:].reshape(logs.shape))
    score = coefficient[0]+(numerator/denominator).sum(axis=1)
    residual = np.maximum(1-labels*score, 0.)
    return float(residual@residual/(2*len(labels))), score


def run(checkpoint, out, seconds, max_step, floor_ratio, chart="log"):
    saved = np.load(checkpoint)
    labels = saved["labels"].astype(float)
    orientation = saved["orientation"].astype(int)
    logs = saved["logs"].copy()
    heads, n = logs.shape
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    start = time.monotonic()
    deadline = start+seconds
    state = evaluate(t, labels, logs, saved["coefficients"])
    events = []
    certificate = None
    iteration = 0
    while time.monotonic() < deadline:
        margin = labels*state["score"]
        np.savez(out/"checkpoint.npz", labels=labels, orientation=orientation,
                 logs=logs, coefficients=state["coefficient"])
        event = dict(iteration=iteration, seconds=time.monotonic()-start,
                     denominator_chart=chart,
                     loss=state["loss"], errors=int((margin <= 0).sum()),
                     minimum_margin=float(margin.min()),
                     inner_gradient=state["inner_gradient"])
        print(json.dumps(dict(phase="start", **event)), flush=True)
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
        gradient, hessian, scale, regularizer, lift = reduced_hessian(
            state, labels, logs, return_lift=True)
        if chart == "affine":
            # For b(t)=b*(1+t*d), log(b(t)) has second derivative -d^2.
            # Convert the reduced log Hessian to relative affine coordinates.
            hessian.flat[::len(hessian)+1] -= gradient/scale
        safer_scale = np.maximum(scale, np.median(scale)*floor_ratio)
        rescale = scale/safer_scale
        gradient *= rescale
        hessian *= rescale[:, None]*rescale[None, :]
        eig, vectors = la.eigh(hessian, subset_by_index=[0, 0], check_finite=False)
        event.update(minimum_eigenvalue=float(eig[0]),
                     reduced_gradient_norm=float(la.norm(gradient)),
                     inner_gram_regularizer=regularizer,
                     scale_floor=float(np.median(scale)*floor_ratio))
        directions = []
        for relative in (1.01, 2., 10.):
            damping = max(1e-5, -float(eig[0])*relative+1e-6)
            shifted = hessian.copy()
            shifted.flat[::len(shifted)+1] += damping
            d = la.solve(shifted, -gradient, assume_a="pos", check_finite=False)
            directions.append((f"newton-{relative}", d/safer_scale))
        if eig[0] < -1e-8:
            directions.extend((f"negative-{s}", s*vectors[:, 0]/safer_scale)
                              for s in (-1, 1))
        directions.append(("gradient", -gradient/safer_scale))
        best = None
        trials = 0
        for name, raw in directions:
            d = raw.reshape(heads, n)
            if chart == "affine":
                d *= min(1., .9/max(float(-d.min()), 1e-30),
                         max_step/max(float(d.max()), 1e-30))
                # Include box clipping in the relative coefficient change.
                d = np.expm1(np.clip(logs+np.log1p(d), -35, 35)-logs)
            else:
                d *= min(1., max_step/max(float(np.max(np.abs(d))), 1e-30))
                d = np.clip(logs+d, -35, 35)-logs
            response = lift@d.ravel()
            for backtrack in range(30):
                if time.monotonic() >= deadline:
                    break
                alpha = 2.**(-backtrack)
                trial_logs = (logs+np.log1p(alpha*d) if chart == "affine"
                              else logs+alpha*d)
                trial_coefficient = state["coefficient"]+alpha*response
                loss, score = quick_evaluate(t, labels, trial_logs, trial_coefficient)
                trials += 1
                if loss < state["loss"]-max(1e-13, 1e-9*state["loss"]):
                    if best is None or loss < best[0]:
                        best = (loss, trial_logs, trial_coefficient, name, alpha)
                    break
        event["cheap_trial_evaluations"] = trials
        event["accepted_direction"] = None if best is None else best[3]
        event["step"] = None if best is None else best[4]
        if best is None:
            events.append(event)
            print(json.dumps(dict(phase="no_descent", **event)), flush=True)
            break
        event["trial_loss"] = best[0]
        print(json.dumps(dict(phase="refit", **event)), flush=True)
        trial_state = evaluate(t, labels, best[1], best[2])
        event["refitted_loss"] = trial_state["loss"]
        event["refit_exceeds_trial"] = trial_state["loss"] > best[0]+1e-8
        event["completed_seconds"] = time.monotonic()-start
        events.append(event)
        print(json.dumps(dict(phase="complete", **event)), flush=True)
        if trial_state["loss"] >= state["loss"]-1e-13:
            break
        state, logs = trial_state, best[1]
        iteration += 1
    np.savez(out/"checkpoint.npz", labels=labels, orientation=orientation,
             logs=logs, coefficients=state["coefficient"])
    result = dict(n=n, heads=heads, seconds=time.monotonic()-start, events=events,
                  denominator_chart=chart,
                  final_loss=state["loss"], certificate=certificate,
                  scope="Finite numerical search. No universal or convergence theorem.",
                  failure_is_not_a_lower_bound=True)
    (out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--max-step", type=float, default=2.)
    parser.add_argument("--floor-ratio", type=float, default=1e-3)
    parser.add_argument("--chart", choices=("log", "affine"), default="log")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.seconds, args.max_step, args.floor_ratio,
        args.chart)
