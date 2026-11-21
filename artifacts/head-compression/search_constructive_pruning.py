#!/usr/bin/env python3
"""Start from a proved face-cover score, then test adaptive head removal.

This is a finite discovery experiment. A successful removal is accepted only
after direct evaluation, and final certificates use independent integer checks.
No claim of a universal pruning theorem is made. Run via heavy.
"""
import argparse
import heapq
import json
import os
from pathlib import Path
import time

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
from search_varpro_scores import convex_hinge_fit
from search_sign_scores import exact_check, integer_pair


def downward_cover(n, rng):
    count = 1 << n
    stars = [[s] + [s ^ (1 << i) for i in range(n) if s >> i & 1]
             for s in range(count)]
    heap = [(-len(v), float(rng.random()), s) for s, v in enumerate(stars)]
    heapq.heapify(heap)
    covered = np.zeros(count, dtype=bool)
    centers, assigned = [], []
    while not covered.all():
        old, tie, s = heapq.heappop(heap)
        fresh = [v for v in stars[s] if not covered[v]]
        if len(fresh) != -old:
            heapq.heappush(heap, (-len(fresh), tie, s))
            continue
        assert fresh
        centers.append(s)
        assigned.append(fresh)
        covered[fresh] = True
    return centers, assigned


def initial_state(n, labels, rng):
    centers, assigned = downward_cover(n, rng)
    mobius = labels.copy()
    for i in range(n):
        for s in range(1 << n):
            if not s >> i & 1:
                mobius[s] -= mobius[s | (1 << i)]
    eps = 1 / (4*n*3**n)
    logs = np.empty((len(centers), n))
    coefficients = np.zeros((len(centers), n+1))
    for h, (s, assigned_h) in enumerate(zip(centers, assigned)):
        logs[h] = [np.log(eps) if s >> i & 1 else -np.log(eps)
                   for i in range(n)]
        for t in assigned_h:
            coefficients[h, 0] += mobius[t]
            if t != s:
                i = (s ^ t).bit_length()-1
                assert s ^ t == 1 << i
                coefficients[h, i+1] -= mobius[t]
    return logs, coefficients, centers, assigned, eps, mobius


def export(n, labels, logs, coefficients, bias):
    heads = []
    for ll, aa in zip(logs, coefficients):
        ai, bi = integer_pair(aa, np.r_[1., np.exp(ll)])
        heads.append({"numerator": ai, "denominator": bi})
    return {"n": n, "labels": labels.astype(int).tolist(), "heads": heads,
            "bias": list(float(bias).as_integer_ratio()),
            "scope": "This finite truth table only; not a universal upper bound."}


class Deadline(Exception):
    pass


def run(n, target, seed, seconds, out):
    start = time.monotonic()
    deadline = start + seconds
    rng = np.random.default_rng(seed)
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    affine = np.column_stack((np.ones(len(x)), x))
    y = rng.choice([-1., 1.], len(x))
    logs, coeff, centers, assigned, eps, mobius = initial_state(n, y, rng)
    bias = 0.
    events = []

    def evaluate(ll, previous=None):
        if time.monotonic() >= deadline:
            raise Deadline
        b = np.exp(ll)
        den = 1+x @ b.T
        features = np.column_stack((np.ones(len(x)),
                    (affine[:, None, :]/den[:, :, None]).reshape(len(x), -1)))
        q, r, piv = la.qr(features, mode="economic", pivoting=True,
                           check_finite=False)
        diagonal = np.abs(np.diag(r))
        rank = int((diagonal > diagonal.max()*1e-12).sum())
        q = q[:, :rank]
        initial = q.T @ y if previous is None else q.T @ previous
        fit = convex_hinge_fit(y[:, None]*q, initial, "newton", 0.)
        # Use a selected full-rank basis. Redundant affine columns are real
        # relations, and must not be treated as independent directions.
        cc = np.zeros(features.shape[1])
        cc[piv[:rank]] = la.solve_triangular(r[:rank, :rank], fit.x,
                                               check_finite=False)
        score = features @ cc
        residual = np.maximum(1-y*score, 0)
        loss = .5*(residual @ residual)/len(y)
        aa = cc[1:].reshape(len(ll), n+1)
        numerator = affine @ aa.T
        grad = np.einsum("x,xh,xi,hi->hi", y*residual,
                         numerator/den**2, x, b)/len(y)
        return loss, grad, aa, cc[0], score, rank

    initial_den = 1+x @ np.exp(logs).T
    initial_score = (affine @ coeff.T / initial_den).sum(1)
    assert np.min(y*initial_score) > .74
    initial = export(n, y, logs, coeff, bias)
    initial_check = exact_check(initial)
    assert initial_check["certified"]
    initial["verification"] = initial_check
    (out/"initial-certificate.json").write_text(json.dumps(initial)+"\n")
    (out/"initial-cover.json").write_text(json.dumps({"n": n,
        "centers": centers, "assigned": assigned, "epsilon": eps,
        "mobius": mobius.astype(int).tolist(), "seed": seed})+"\n")
    best = (logs.copy(), coeff.copy(), bias, initial_score.copy())
    initial_heads = len(logs)
    stage = 0
    try:
        while len(logs) > target:
            old_logs, old_coeff, old_bias, old_score = best
            old_h = len(old_logs)
            contribution = affine @ old_coeff.T / (1+x @ np.exp(old_logs).T)
            influence = np.ptp(contribution, axis=0)
            # A finite heuristic, not a claim that range predicts redundancy.
            remove_count = max(1, min(old_h-target, old_h//20))
            accepted = False
            for attempt in range(4):
                if attempt == 0:
                    chosen = np.argsort(influence)[:remove_count]
                else:
                    candidates = np.argsort(influence)[:max(remove_count, old_h//3)]
                    chosen = rng.choice(candidates, remove_count, replace=False)
                keep = np.ones(old_h, dtype=bool)
                keep[chosen] = False
                trial_logs = old_logs[keep].copy()
                trial_best = [float("inf"), None]
                evaluations = [0]

                def objective(flat):
                    ll = flat.reshape(-1, n)
                    result = evaluate(ll, old_score)
                    evaluations[0] += 1
                    if result[0] < trial_best[0]:
                        trial_best[:] = [result[0], (ll.copy(), *result[2:])]
                    return result[0], result[1].ravel()

                first = evaluate(trial_logs, old_score)
                trial_best[:] = [first[0], (trial_logs.copy(), *first[2:])]
                if np.min(y*first[4]) <= 1e-5:
                    opt.minimize(objective, trial_logs.ravel(), jac=True,
                        method="L-BFGS-B", bounds=[(-25, 25)]*trial_logs.size,
                        options={"maxiter": 100, "maxls": 30, "maxcor": 30,
                                 "ftol": 1e-13, "gtol": 1e-10})
                ll, aa, bb, ss, rank = trial_best[1]
                margin = y*ss
                event = {"stage": stage, "attempt": attempt,
                         "seconds": time.monotonic()-start, "heads": len(ll),
                         "removed": remove_count, "loss": trial_best[0],
                         "errors": int((margin <= 0).sum()),
                         "minimum_margin": float(margin.min()),
                         "rank": rank, "evaluations": evaluations[0]}
                events.append(event)
                print(json.dumps(event), flush=True)
                if margin.min() > 1e-5:
                    cert = export(n, y, ll, aa, bb)
                    checked = exact_check(cert)
                    if checked["certified"]:
                        cert["verification"] = checked
                        (out/"best-certificate.json").write_text(json.dumps(cert)+"\n")
                        best = (ll, aa, bb, ss)
                        logs = ll
                        accepted = True
                        np.savez(out/"best-checkpoint.npz", logs=ll,
                            full_coefficients=aa, bias=bb, labels=y,
                            orientation=np.ones(len(ll), dtype=int))
                        break
                if remove_count > 1:
                    remove_count = max(1, remove_count//2)
            if not accepted:
                break
            stage += 1
    except Deadline:
        pass
    result = {"n": n, "seed": seed, "target": target,
              "initial_heads": initial_heads, "best_certified_heads": len(best[0]),
              "seconds": time.monotonic()-start, "events": events,
              "scope": "Finite instance only; failure is not a lower bound."}
    (out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--n", type=int, required=True)
    p.add_argument("--target", type=int, required=True)
    p.add_argument("--seed", type=int, default=440000)
    p.add_argument("--seconds", type=float, default=7200)
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.n, args.target, args.seed, args.seconds, args.out)
