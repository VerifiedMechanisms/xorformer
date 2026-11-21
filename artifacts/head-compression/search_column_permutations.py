#!/usr/bin/env python3
"""Finite head search by permuting slope columns within each orientation.

The multiset in every denominator column is preserved exactly. This is a
diagnostic for a discrete encoding family, not a universal construction.
Only fully rebuilt numerator refits with lower hinge loss are accepted.
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
from search_reduced_curvature import evaluate
from search_newton_scores import export
from search_sign_scores import exact_check


def denominator_gradient(state, labels, logs):
    count, heads, n = state["local"].shape
    head_scores = np.einsum("xhi,hi->xh", state["local"],
                            state["coefficient"][1:].reshape(heads, n))
    weight = labels*state["residual"]
    return np.einsum("xhi,xh,x->hi", state["local"]*np.exp(logs)[None],
                     head_scores, weight)/count


def proposals(logs, orientation, gradient, rng, count):
    heads, n = logs.shape
    bank = []
    for i in rng.permutation(n):
        for o in (-1, 1):
            ids = np.flatnonzero(orientation == o)
            if len(ids) < 2:
                continue
            value = logs[ids, i]
            grad = gradient[ids, i]
            delta = value[None, :]-value[:, None]
            prediction = (grad[:, None]-grad[None, :])*delta
            for width in (.05, .2, .8, 3., np.inf):
                allowed = np.triu((np.abs(delta) <= width) &
                                   (np.abs(delta) > 1e-8), 1)
                cost = np.where(allowed, prediction, np.inf)
                a, b = np.unravel_index(np.argmin(cost), cost.shape)
                if np.isfinite(cost[a, b]):
                    bank.append((float(cost[a, b]), int(i), int(ids[a]), int(ids[b])))
    # Repeated width thresholds often identify the same swap.
    unique = {}
    for item in bank:
        unique[item[1:]] = item
    ranked = sorted(unique.values())
    large = ranked[:max(1, count//2)]
    remaining = ranked[len(large):]
    short = []
    if remaining:
        # Also test short swaps, rather than only the largest linear prediction.
        remaining.sort(key=lambda v: abs(logs[v[2], v[1]]-logs[v[3], v[1]]))
        short = remaining[:count-len(large)]
    selected = []
    for j in range(max(len(large), len(short))):
        if j < len(large):
            selected.append(large[j])
        if j < len(short):
            selected.append(short[j])
    return selected


def run(checkpoint, out, seconds, seed, candidates):
    saved = np.load(checkpoint)
    labels = saved["labels"].astype(float)
    logs = saved["logs"].copy()
    orientation = saved["orientation"].astype(int)
    heads, n = logs.shape
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    original_multisets = {o: np.sort(logs[orientation == o], axis=0)
                          for o in (-1, 1)}
    rng = np.random.default_rng(seed)
    start = time.monotonic()
    deadline = start+seconds
    state = evaluate(t, labels, logs, saved["coefficients"])
    events = []
    certificate = None
    rejected = set()
    iteration = 0
    while time.monotonic() < deadline:
        np.savez(out/"checkpoint.npz", labels=labels, logs=logs,
                 orientation=orientation, coefficients=state["coefficient"])
        margin = labels*state["score"]
        print(json.dumps(dict(phase="start", iteration=iteration,
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
        gradient = denominator_gradient(state, labels, logs)
        bank = proposals(logs, orientation, gradient, rng, 10*candidates)
        bank = [p for p in bank if p[1:] not in rejected][:candidates]
        if not bank:
            break
        best = None
        event = dict(iteration=iteration, original_loss=state["loss"], trials=[])
        for predicted, i, a, b in bank:
            if time.monotonic() >= deadline:
                break
            candidate = logs.copy()
            candidate[a, i], candidate[b, i] = candidate[b, i], candidate[a, i]
            fit = evaluate(t, labels, candidate, solver="lbfgs",
                           initial_score=state["score"])
            event["trials"].append(dict(column=i, first=a, second=b,
                                         prediction=predicted, loss=fit["loss"],
                                         inner_gradient=fit["inner_gradient"]))
            print(json.dumps(dict(phase="trial", iteration=iteration,
                                  seconds=time.monotonic()-start,
                                  **event["trials"][-1])), flush=True)
            rejected.add((i, a, b))
            if fit["loss"] < state["loss"]-1e-9 and (
                    best is None or fit["loss"] < best[0]["loss"]):
                best = (fit, candidate)
        event["accepted"] = best is not None
        if best is not None:
            state, logs = best
            rejected.clear()
        for o in (-1, 1):
            assert np.array_equal(np.sort(logs[orientation == o], axis=0),
                                  original_multisets[o])
        event["seconds"] = time.monotonic()-start
        events.append(event)
        print(json.dumps(event), flush=True)
        iteration += 1
    np.savez(out/"checkpoint.npz", labels=labels, logs=logs,
             orientation=orientation, coefficients=state["coefficient"])
    result = dict(n=n, heads=heads, seconds=time.monotonic()-start,
                  final_loss=state["loss"], certificate=certificate, events=events,
                  scope="One finite truth table and fixed slope multisets only.",
                  failure_is_not_a_lower_bound=True)
    (out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--seed", type=int, default=580014)
    parser.add_argument("--candidates", type=int, default=6)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.seconds, args.seed, args.candidates)
