#!/usr/bin/env python3
"""Conditional max-min margin search by linear-program feasibility.

For fixed other heads F and a proposed margin mu, the inequalities
f(x) * (F(x) * B(x) + A(x)) >= mu * B(x) are linear in A and B.
Both admissible orientations are tried. Denominator coefficients lie in a
truncated simplex, so this numerical search is a restricted experiment.
It is not a global convergence theorem. Run through heavy.
"""
import argparse
import json
import os
from pathlib import Path
import time

for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
from scipy.optimize import linprog
from search_newton_scores import export
from search_sign_scores import exact_check


def completion_program(design, labels, fixed, seconds):
    """Maximize a common strict slack in denominator and cleared signs.

    In exact arithmetic, optimum rho > 0 is equivalent to completion by
    one head of this orientation. Numerical status alone is not a proof.
    """
    count, dimension = design.shape
    matrix = np.column_stack((-labels[:, None]*design,
                              -(labels*fixed)[:, None]*design,
                              np.ones(count)))
    coefficient_constraints = np.column_stack((np.zeros((dimension, dimension)),
                                                -np.eye(dimension),
                                                np.ones(dimension)))
    matrix = np.vstack((matrix, coefficient_constraints))
    matrix /= np.maximum(np.max(np.abs(matrix), axis=1), 1.)[:, None]
    equality = np.r_[np.zeros(dimension), np.ones(dimension), 0.][None, :]
    return linprog(np.r_[np.zeros(2*dimension), -1.], A_ub=matrix,
                   b_ub=np.zeros(count+dimension), A_eq=equality,
                   b_eq=np.ones(1),
                   bounds=[(None, None)]*dimension + [(0., None)]*(dimension+1),
                   method="highs", options={"time_limit": seconds,
                       "primal_feasibility_tolerance": 1e-9,
                       "dual_feasibility_tolerance": 1e-9})


def run(args):
    data = np.load(args.checkpoint)
    y = data["labels"].astype(float)
    orientation = data["orientation"].astype(int).copy()
    n, heads = len(y).bit_length() - 1, len(orientation)
    assert len(y) == 1 << n
    slopes = np.exp(data["logs"].reshape(heads, n))
    coef = data["coefficients"]
    bias = float(coef[0])
    aa = np.column_stack((np.zeros(heads), coef[1:].reshape(heads, n)))
    bb = np.column_stack((np.ones(heads), slopes))
    gauge = bb.sum(axis=1)
    aa /= gauge[:, None]
    bb /= gauge[:, None]
    x = ((np.arange(len(y))[:, None] >> np.arange(n)) & 1).astype(float)
    designs = {1: np.column_stack((np.ones(len(y)), x)),
               -1: np.column_stack((np.ones(len(y)), 1-x))}
    pieces = np.column_stack([(designs[int(orientation[h])] @ aa[h]) /
                             (designs[int(orientation[h])] @ bb[h])
                             for h in range(heads)])
    score = bias + pieces.sum(axis=1)
    rng = np.random.default_rng(args.seed)
    started = time.monotonic()
    deadline = started + args.seconds
    records = []
    certificate = None
    sweep = 0
    equality = np.r_[np.zeros(n+1), np.ones(n+1)][None, :]
    bounds = [(None, None)]*(n+1) + [(args.epsilon, 1.)]*(n+1)

    def save():
        canonical_slopes = bb[:, 1:] / bb[:, :1]
        constants = aa[:, 0] / bb[:, 0]
        canonical_a = aa[:, 1:]/bb[:, :1] - constants[:, None]*canonical_slopes
        canonical_bias = bias + constants.sum()
        np.savez(args.out/"checkpoint.npz", labels=y, orientation=orientation,
                 logs=np.log(canonical_slopes),
                 coefficients=np.r_[canonical_bias, canonical_a.ravel()])
        return canonical_bias, canonical_a, canonical_slopes

    while time.monotonic() < deadline:
        accepted = 0
        for h in rng.permutation(heads):
            if time.monotonic() >= deadline:
                break
            fixed = score - pieces[:, h]
            old_margin = float((y*score).min())
            best_margin = old_margin
            best = None
            lp_statuses = []
            for sign in [int(orientation[h]), -int(orientation[h])]:
                design = designs[sign]
                completion = completion_program(design, y, fixed,
                    min(args.lp_seconds, max(1., deadline-time.monotonic())))
                lp_statuses.append(int(completion.status))
                if completion.x is not None and np.all(np.isfinite(completion.x)):
                    a, b = completion.x[:n+1], completion.x[n+1:2*n+2]
                    if np.all(b > 0):
                        piece = (design @ a)/(design @ b)
                        candidate = fixed + piece
                        minimum = float((y*candidate).min())
                        if minimum > max(best_margin+1e-8, 1e-10):
                            best_margin = minimum
                            best = (sign, a.copy(), b.copy(), piece, candidate)
                            break
                lower, upper = old_margin, max(1e-4, old_margin+1.)
                target = 1e-4 if old_margin < 1e-4 else upper
                for step in range(args.bisections):
                    if time.monotonic() >= deadline:
                        break
                    matrix = np.column_stack((-y[:, None]*design,
                                               (target-y*fixed)[:, None]*design))
                    # Positive row scaling preserves the feasibility problem.
                    row_scale = np.maximum(np.max(np.abs(matrix), axis=1), 1.)
                    matrix /= row_scale[:, None]
                    fit = linprog(np.zeros(2*n+2), A_ub=matrix,
                                  b_ub=np.zeros(len(y)), A_eq=equality,
                                  b_eq=np.ones(1), bounds=bounds, method="highs",
                                  options={"time_limit": min(args.lp_seconds,
                                      max(1., deadline-time.monotonic())),
                                      "primal_feasibility_tolerance": 1e-9,
                                      "dual_feasibility_tolerance": 1e-9})
                    lp_statuses.append(int(fit.status))
                    valid = False
                    if fit.x is not None and np.all(np.isfinite(fit.x)):
                        a, b = fit.x[:n+1], fit.x[n+1:]
                        if np.all(b > 0):
                            piece = (design @ a)/(design @ b)
                            candidate = fixed + piece
                            minimum = float((y*candidate).min())
                            valid = minimum >= target-1e-7
                            if minimum > best_margin + 1e-8:
                                best_margin = minimum
                                best = (sign, a.copy(), b.copy(), piece, candidate)
                    if valid:
                        lower = target
                        if lower > 1e-6:
                            break
                    else:
                        upper = target
                    target = (lower+upper)/2
                if best_margin > 1e-6:
                    break
            event = {"sweep": sweep, "head": int(h),
                     "seconds": time.monotonic()-started,
                     "old_minimum_margin": old_margin,
                     "minimum_margin": best_margin,
                     "lp_statuses": lp_statuses}
            if best is not None:
                sign, a, b, piece, candidate = best
                event["orientation_changed"] = bool(sign != orientation[h])
                orientation[h], aa[h], bb[h] = sign, a, b
                pieces[:, h], score = piece, candidate
                accepted += 1
            event["errors"] = int((y*score <= 0).sum())
            event["hinge_loss"] = float(np.maximum(1-y*score, 0).mean())
            records.append(event)
            print(json.dumps(event), flush=True)
            if (y*score).min() > 1e-10:
                cb, ca, cs = save()
                cert = export(n, y, ca, cs, orientation, cb)
                check = exact_check(cert)
                if check["certified"]:
                    cert["verification"] = check
                    certificate = args.out/"certificate.json"
                    certificate.write_text(json.dumps(cert, indent=2)+"\n")
                    break
        save()
        # Refresh accumulated floating-point sums before another sweep.
        score = bias + pieces.sum(axis=1)
        sweep += 1
        if certificate is not None or accepted == 0:
            break
    result = {"n": n, "heads": heads, "sweeps": sweep,
              "seconds": time.monotonic()-started, "epsilon": args.epsilon,
              "minimum_margin": float((y*score).min()),
              "errors": int((y*score <= 0).sum()),
              "certificate": str(certificate) if certificate else None,
              "scope": "Restricted finite search. No global optimality or universal bound."}
    (args.out/"events.json").write_text(json.dumps(records, indent=2)+"\n")
    (args.out/"result.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("checkpoint", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=14400.)
    p.add_argument("--seed", type=int, default=470000)
    p.add_argument("--epsilon", type=float, default=1e-10)
    p.add_argument("--lp-seconds", type=float, default=60.)
    p.add_argument("--bisections", type=int, default=7)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args)
