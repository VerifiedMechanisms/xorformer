#!/usr/bin/env python3
"""Replace heads using QR deletion and residual-directed candidate poles.

Only measured decreases of the full finite squared-hinge objective are
accepted. Neither deletion estimates nor candidate correlations certify
progress. A successful sign table must pass the integer export checker.
Run substantial instances through heavy.
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
from search_reduced_curvature import evaluate
from search_varpro_scores import convex_hinge_fit
from search_newton_scores import export
from search_sign_scores import exact_check


def fit_q(q, labels, initial_score):
    fitted = convex_hinge_fit(labels[:, None]*q, q.T@initial_score, "lbfgs", 0.)
    score = q@fitted.x
    residual = np.maximum(1-labels*score, 0.)
    return dict(q=q, coordinate=fitted.x, score=score,
                residual=residual, loss=float(residual@residual/(2*len(labels))),
                inner_gradient=float(np.max(np.abs(fitted.jac))))


def residual_atom(logs, x, residual):
    """Negative least-squares projection energy and its envelope derivative."""
    b = np.exp(logs)
    denominator = 1+x@b
    f = x/denominator[:, None]
    a = la.lstsq(f, residual, cond=1e-12, check_finite=False,
                 lapack_driver="gelsy")[0]
    s = f@a
    value = -float(s@s)/len(x)
    probability = f*b[None, :]
    gradient = 2*probability.T@((residual-s)*s)/len(x)
    return value, gradient


def deletion_order(state, heads, n):
    """Rank removals by full-cube squared score distance, not hinge loss."""
    inverse = la.solve_triangular(state["triangular"],
                                  np.eye(1+heads*n), check_finite=False)
    coordinate = state["q"].T@state["score"]
    distances = []
    for h in range(heads):
        z, _ = la.qr(inverse[1+h*n:1+(h+1)*n].T,
                     mode="economic", check_finite=False)
        distance = float(la.norm(z.T@coordinate)**2)/(2*len(state["score"]))
        distances.append(distance)
    return np.argsort(distances), distances


def run(checkpoint, out, seconds, seed, starts, candidates):
    saved = np.load(checkpoint)
    labels = saved["labels"].astype(float)
    logs = saved["logs"].copy()
    orientation = saved["orientation"].astype(int)
    heads, n = logs.shape
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    rng = np.random.default_rng(seed)
    start = time.monotonic()
    deadline = start+seconds
    state = evaluate(t, labels, logs, saved["coefficients"])
    events = []
    certificate = None
    round_number = 0
    while time.monotonic() < deadline:
        np.savez(out/"checkpoint.npz", labels=labels, logs=logs,
                 orientation=orientation, coefficients=state["coefficient"])
        margin = labels*state["score"]
        print(json.dumps(dict(phase="round", round=round_number,
                              seconds=time.monotonic()-start, loss=state["loss"],
                              errors=int((margin <= 0).sum()),
                              minimum_margin=float(margin.min()))), flush=True)
        if margin.min() > 1e-5:
            cert = export(n, labels, state["coefficient"][1:].reshape(heads, n),
                          np.exp(logs), orientation, state["coefficient"][0])
            check = exact_check(cert)
            if check["certified"]:
                cert["verification"] = check
                (out/"certificate.json").write_text(json.dumps(cert)+"\n")
                certificate = "certificate.json"
                break
        order, distances = deletion_order(state, heads, n)
        accepted = False
        # Inspect a different short list after an unsuccessful pass.
        offset = (round_number % max(1, heads//4))*4
        for h in order[offset:offset+4]:
            if time.monotonic() >= deadline:
                break
            h = int(h)
            qm, rm = la.qr_delete(state["q"], state["triangular"],
                                  1+h*n, n, which="col", check_finite=False)
            removed = fit_q(qm, labels, state["score"])
            residual = labels*removed["residual"]
            bank = []
            for trial in range(starts):
                if time.monotonic() >= deadline:
                    break
                o = int(orientation[h]) if trial < starts//2 else -int(orientation[h])
                tx = x if o > 0 else 1-x
                initial = (logs[h]+rng.normal(0, 2, n) if trial % 2 == 0
                           else rng.normal(-1, 4, n))
                fit = opt.minimize(residual_atom, np.clip(initial, -30, 30),
                                   args=(tx, residual), jac=True, method="L-BFGS-B",
                                   bounds=[(-30, 30)]*n,
                                   options={"maxiter": 180, "gtol": 1e-12,
                                            "ftol": 1e-14, "maxls": 35})
                bank.append((float(fit.fun), fit.x.copy(), o))
            bank.sort(key=lambda item: item[0])
            event = dict(round=round_number, head=h, deletion_distance=distances[h],
                         original_loss=state["loss"], removed_loss=removed["loss"],
                         candidate_energies=[v[0] for v in bank], trials=[])
            best = None
            for energy, new_log, o in bank[:candidates]:
                if time.monotonic() >= deadline:
                    break
                tx = x if o > 0 else 1-x
                f = tx/(1+tx@np.exp(new_log))[:, None]
                try:
                    qn, rn = la.qr_insert(qm, rm, f, len(rm), which="col",
                                          rcond=1e-15, check_finite=False)
                except la.LinAlgError:
                    event["trials"].append(dict(energy=energy, rejected="rank"))
                    continue
                fitted = fit_q(qn, labels, removed["score"])
                event["trials"].append(dict(energy=energy, loss=fitted["loss"],
                                             inner_gradient=fitted["inner_gradient"]))
                if fitted["loss"] < state["loss"]-1e-9 and (
                        best is None or fitted["loss"] < best[0]["loss"]):
                    best = (fitted, new_log, o, rn)
            event["candidate_improved"] = best is not None
            event["accepted"] = False
            if best is not None:
                fitted, new_log, o, rn = best
                new_logs = np.vstack((np.delete(logs, h, axis=0), new_log))
                new_orientation = np.append(np.delete(orientation, h), o)
                coefficient = la.solve_triangular(rn, fitted["coordinate"],
                                                   check_finite=False)
                new_t = np.where(new_orientation[None, :, None] > 0,
                                 x[:, None], 1-x[:, None])
                # Rebuild the QR factorization before accepting, so incremental
                # QR drift cannot by itself produce a claimed improvement.
                audited = evaluate(new_t, labels, new_logs, coefficient)
                event["rebuilt_loss"] = audited["loss"]
                if audited["loss"] < state["loss"]-1e-9:
                    logs, orientation, t, state = new_logs, new_orientation, new_t, audited
                    accepted = True
                    event["accepted"] = True
            event["seconds"] = time.monotonic()-start
            events.append(event)
            print(json.dumps(event), flush=True)
            if accepted:
                break
        round_number += 1
        if not accepted and offset+4 >= heads:
            break
    np.savez(out/"checkpoint.npz", labels=labels, logs=logs,
             orientation=orientation, coefficients=state["coefficient"])
    result = dict(n=n, heads=heads, seconds=time.monotonic()-start, events=events,
                  final_loss=state["loss"], certificate=certificate,
                  scope="Finite search only. No universal or convergence claim.",
                  failure_is_not_a_lower_bound=True)
    (out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--seed", type=int, default=570014)
    parser.add_argument("--starts", type=int, default=12)
    parser.add_argument("--candidates", type=int, default=4)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.seconds, args.seed, args.starts, args.candidates)
