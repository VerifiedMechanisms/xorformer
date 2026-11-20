#!/usr/bin/env python3
"""Backtracking and sampled-gradient search for admissible rational signs.

Every function/gradient evaluation uses the Arb primal/dual refit. A failed
LP or refit causes a smaller trial step, not a claimed infeasibility result.
Sampled gradients are a heuristic for nonsmooth points, with no convergence
claim. Only independent exact rational checking can certify a truth table.
Run through heavy with python-flint available on PYTHONPATH.
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
from search_arb_hinge import ArbProblem
from search_varpro_scores import TimeLimit, Certified


def direction_from_history(gradient, history):
    q = gradient.copy()
    coefficients = []
    for s, y, rho in reversed(history):
        alpha = rho * (s @ q)
        coefficients.append(alpha)
        q -= alpha*y
    if history:
        s, y, _ = history[-1]
        q *= (s @ y)/(y @ y)
    for (s, y, rho), alpha in zip(history, reversed(coefficients)):
        q += s*(alpha-rho*(y @ q))
    return -q


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=25200)
    parser.add_argument("--bits", type=int, default=512)
    parser.add_argument("--lp-seconds", type=float, default=30)
    parser.add_argument("--max-step", type=float, default=.01)
    parser.add_argument("--samples", type=int, default=32)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    saved = np.load(args.checkpoint)
    labels, orientation = saved["labels"], saved["orientation"]
    point = saved["logs"].ravel().copy()
    n, h = len(labels).bit_length()-1, len(orientation)
    problem = ArbProblem(n, h, 210000, args.seconds, args.out,
                         "arb_backtrack", score_penalty=0)
    problem.bits, problem.lp_seconds = args.bits, args.lp_seconds
    problem.y, problem.orientation = labels.copy(), orientation.copy()
    problem.initial_logs = point.copy()
    rng = np.random.default_rng(210000)
    history, records = [], []
    step_bound, sample_radius = args.max_step, 1e-5
    rejected = 0
    try:
        loss, gradient = problem.objective(point)
        iteration = 0
        while time.monotonic() < problem.deadline:
            direction = direction_from_history(gradient, history)
            if gradient @ direction >= 0 or not np.isfinite(direction).all():
                direction, history = -gradient.copy(), []
            maximum = np.abs(direction).max()
            if maximum:
                direction *= min(1., step_bound/maximum)
            accepted = False
            for backtrack in range(24):
                trial = np.clip(point+(2.**-backtrack)*direction, -20, 20)
                if np.array_equal(point, trial):
                    break
                try:
                    trial_loss, trial_gradient = problem.objective(trial)
                except ArithmeticError as error:
                    rejected += 1
                    print(json.dumps({"rejected_trial": str(error),
                                      "backtrack": backtrack}), flush=True)
                    continue
                step = trial-point
                if trial_loss <= loss+1e-4*(gradient @ step):
                    change = trial_gradient-gradient
                    curvature = step @ change
                    if curvature > 1e-10*la.norm(step)*la.norm(change):
                        history.append((step.copy(), change.copy(), 1/curvature))
                        history = history[-12:]
                    else:
                        history = []
                    point, loss, gradient = trial, trial_loss, trial_gradient
                    accepted = True
                    step_bound = min(args.max_step, 1.2*step_bound)
                    break
            record = {"iteration": iteration, "accepted": accepted,
                      "loss": loss, "step_bound": step_bound,
                      "gradient_norm": float(la.norm(gradient)),
                      "rejected_trials": rejected}
            records.append(record)
            print(json.dumps(record), flush=True)
            iteration += 1
            if accepted:
                continue
            history = []
            gradients = [gradient.copy()]
            improved = None
            for sample in range(args.samples):
                offset = rng.normal(size=point.shape)
                offset *= sample_radius/la.norm(offset)
                candidate = np.clip(point+offset, -20, 20)
                try:
                    candidate_loss, candidate_gradient = problem.objective(candidate)
                except ArithmeticError:
                    rejected += 1
                    continue
                gradients.append(candidate_gradient)
                if candidate_loss < loss and (improved is None or candidate_loss < improved[1]):
                    improved = candidate, candidate_loss, candidate_gradient
            if improved is not None:
                point, loss, gradient = improved
                continue
            matrix = np.asarray(gradients)
            gram = matrix @ matrix.T
            count = len(gradients)
            fit = opt.minimize(lambda w: (.5*float(w @ gram @ w), gram @ w),
                               np.full(count, 1/count), jac=True, method="SLSQP",
                               bounds=[(0.,1.)]*count,
                               constraints={"type":"eq", "fun":lambda w:w.sum()-1,
                                            "jac":lambda w:np.ones_like(w)},
                               options={"maxiter":500, "ftol":1e-15})
            if fit.success:
                gradient = fit.x @ matrix
            step_bound *= .25
            sample_radius *= .5
            print(json.dumps({"sampled_gradients": count,
                              "sampled_direction_norm": float(la.norm(gradient)),
                              "sample_radius": sample_radius}), flush=True)
            if step_bound < 1e-12:
                break
        reason = "time or step limit"
    except Certified:
        reason = "independently certified finite truth table"
    except TimeLimit:
        reason = "time limit"
    except ArithmeticError as error:
        reason = "initial basis failure: "+str(error)
    result = {"reason": reason, "best_loss": problem.best_loss,
              "certificate": problem.certificate, "iterations": records,
              "evaluations": problem.evaluations,
              "seconds": time.monotonic()-problem.start,
              "failure_is_not_a_lower_bound": True}
    (args.out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "iterations"}), flush=True)


if __name__ == "__main__":
    main()
