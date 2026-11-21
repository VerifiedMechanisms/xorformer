#!/usr/bin/env python3
"""Explore single-head rational hinge descent using linear programs.

Each LP minimizes the exact first-order convex surrogate proved in the
mechanism audit, with a coefficient trust box. An actual rational-loss line
search accepts only decreases. This is a finite numerical experiment, not a
convergence theorem. Any success must pass the independent exact checker.
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
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, diags, hstack
from search_newton_scores import export
from search_sign_scores import exact_check


def run(checkpoint, out, seconds, seed, trust, lp_seconds):
    saved = np.load(checkpoint)
    y = saved["labels"].astype(float)
    orientation = saved["orientation"].astype(int)
    n, heads = len(y).bit_length()-1, len(orientation)
    assert len(y) == 1 << n
    slopes = np.exp(saved["logs"].reshape(heads, n))
    oldcoef = saved["coefficients"]
    bias = float(oldcoef[0])
    numerators = np.column_stack((np.zeros(heads), oldcoef[1:].reshape(heads, n)))
    x = ((np.arange(len(y))[:, None] >> np.arange(n)) & 1).astype(float)
    t = np.where(orientation[None, :, None] > 0, x[:, None, :], 1-x[:, None, :])
    denominator = 1+np.einsum("xhi,hi->xh", t, slopes)
    numerator = numerators[:, 0]+np.einsum("xhi,hi->xh", t, numerators[:, 1:])
    contributions = numerator/denominator
    score = bias+contributions.sum(axis=1)
    rng = np.random.default_rng(seed)
    started = time.monotonic()
    deadline = started+seconds
    events = []
    certificate = None
    sweep = 0

    def save():
        # A/B = a0 + sum_i (ai-a0*bi)*ti/B.
        canonical_bias = bias+numerators[:, 0].sum()
        canonical_a = numerators[:, 1:]-numerators[:, :1]*slopes
        np.savez(out/"checkpoint.npz", labels=y, orientation=orientation,
                 logs=np.log(slopes), coefficients=np.r_[canonical_bias, canonical_a.ravel()])
        return canonical_bias, canonical_a

    while time.monotonic() < deadline:
        accepted = 0
        for h in rng.permutation(heads):
            if time.monotonic() >= deadline:
                break
            th = t[:, h, :]
            xa = np.column_stack((np.ones(len(y)), th))
            bh = denominator[:, h]
            residual_score = score-contributions[:, h]
            margin = y*score
            hinge = np.maximum(1-margin, 0)
            old_loss = float(hinge.mean())
            # s_x is the cleared hinge divided by the OLD denominator.
            # Its linear denominator correction makes the surrogate tangent
            # to the actual rational hinge, including directional derivatives
            # at its kinks.
            matrix = hstack((csr_matrix(-y[:, None]*xa/bh[:, None]),
                             csr_matrix((1-y*residual_score)[:, None]*th/bh[:, None]),
                             -diags(np.ones(len(y)))), format="csr")
            rhs = (y*residual_score-1)/bh
            objective = np.r_[np.zeros(n+1), -(hinge/bh)@th/len(y),
                               np.ones(len(y))/len(y)]
            bounds = [(None, None)]*(n+1)
            bounds += [(max(float(v/trust), 1e-12), min(float(v*trust), 1e12))
                       for v in slopes[h]]
            bounds += [(0, None)]*len(y)
            fit = linprog(objective, A_ub=matrix, b_ub=rhs, bounds=bounds,
                          method="highs", options={"time_limit": min(lp_seconds, max(1., deadline-time.monotonic()))})
            event = {"sweep": sweep, "head": int(h), "seconds": time.monotonic()-started,
                     "status": int(fit.status), "message": fit.message,
                     "old_loss": old_loss, "old_errors": int((margin <= 0).sum())}
            if fit.x is not None and np.all(np.isfinite(fit.x)):
                aa = fit.x[:n+1]
                bb = np.maximum(fit.x[n+1:2*n+1], 1e-12)
                full_den = 1+th@bb
                full_num = xa@aa
                delta = (np.maximum((1-y*residual_score)*full_den-y*full_num, 0)/bh
                         -hinge-hinge*(full_den/bh-1))
                gain = -float(delta.mean())
                modulus = float(np.abs(full_den/bh-1).max())
                total_variation = float(np.abs(delta).mean())
                event["surrogate_gain"] = gain
                steps = [2.**(-power) for power in range(18)]
                if gain > 0 and modulus > 0 and total_variation > 0:
                    steps.append(min(1., 1/(2*modulus), gain/(4*modulus*total_variation)))
                best = (old_loss, 0., None, None, None, None)
                for alpha in steps:
                    a = (1-alpha)*numerators[h]+alpha*aa
                    b = (1-alpha)*slopes[h]+alpha*bb
                    den = 1+th@b
                    piece = (xa@a)/den
                    candidate = residual_score+piece
                    loss = float(np.maximum(1-y*candidate, 0).mean())
                    if loss < best[0]-1e-12:
                        best = (loss, alpha, a, b, den, piece)
                if best[1] > 0:
                    loss, alpha, a, b, den, piece = best
                    numerators[h], slopes[h] = a, b
                    denominator[:, h], contributions[:, h] = den, piece
                    score = residual_score+piece
                    accepted += 1
                    event.update({"loss": loss, "alpha": alpha,
                                  "errors": int((y*score <= 0).sum()),
                                  "minimum_margin": float((y*score).min())})
            events.append(event)
            print(json.dumps(event), flush=True)
            if (y*score).min() > 1e-6:
                cb, ca = save()
                cert = export(n, y, ca, slopes, orientation, cb)
                check = exact_check(cert)
                if check["certified"]:
                    cert["verification"] = check
                    certificate = out/"certificate.json"
                    certificate.write_text(json.dumps(cert, indent=2)+"\n")
                    break
        save()
        sweep += 1
        if certificate is not None or accepted == 0:
            break
    result = {"n": n, "heads": heads, "sweeps": sweep,
              "seconds": time.monotonic()-started, "lp_calls": len(events),
              "hinge_loss": float(np.maximum(1-y*score, 0).mean()),
              "errors": int((y*score <= 0).sum()),
              "minimum_margin": float((y*score).min()),
              "certificate": str(certificate) if certificate else None,
              "scope": "This checkpoint and target only. Failure is not a lower bound."}
    (out/"events.json").write_text(json.dumps(events, indent=2)+"\n")
    (out/"result.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=14400.)
    parser.add_argument("--seed", type=int, default=420000)
    parser.add_argument("--trust", type=float, default=4.)
    parser.add_argument("--lp-seconds", type=float, default=120.)
    args = parser.parse_args()
    assert args.trust > 1
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.seconds, args.seed, args.trust, args.lp_seconds)
