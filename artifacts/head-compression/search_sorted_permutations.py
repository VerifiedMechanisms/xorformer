#!/usr/bin/env python3
"""Finite slope-multiset search using exact quadratic permutation proposals.

Sorting projects a gradient step onto each column's permutation orbit.
The proposal is not a convergence theorem. Only a measured decrease after
rebuilding the numerator fit is accepted. Run substantial jobs through heavy.
"""
import argparse
import json
import os
from pathlib import Path
import time

for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
from search_column_permutations import denominator_gradient
from search_reduced_curvature import evaluate
from search_newton_scores import export
from search_sign_scores import exact_check


def project_column(values, gradient, step):
    order = np.argsort(values-step*gradient, kind="stable")
    answer = np.empty_like(values)
    answer[order] = np.sort(values)
    return answer


def bounded_proposal(logs, orientation, gradient, column, width):
    candidate = logs.copy()
    for sign in (-1, 1):
        ids = np.flatnonzero(orientation == sign)
        if len(ids) < 2:
            continue
        value, grad = logs[ids, column], gradient[ids, column]
        scale = max(float(np.ptp(grad)), 1e-30)
        step = width/scale
        best = value.copy()
        # Geometric trials avoid assuming that maximum displacement is
        # monotone along the projection path.
        for factor in (32., 8., 2., .5, .125, .03125):
            trial = project_column(value, grad, factor*step)
            if np.max(np.abs(trial-value)) <= width:
                if grad@(trial-value) < grad@(best-value):
                    best = trial
        candidate[ids, column] = best
    delta = candidate-logs
    return candidate, float(np.sum(gradient*delta))


def proposals(logs, orientation, gradient, count):
    bank, seen = [], set()
    for width in (.01, .03, .1, .3, 1., 3.):
        for column in range(logs.shape[1]):
            candidate, prediction = bounded_proposal(
                logs, orientation, gradient, column, width)
            key = candidate[:, column].tobytes(), column
            if prediction >= -1e-14 or key in seen:
                continue
            seen.add(key)
            delta = candidate-logs
            bank.append((prediction, column, float(np.max(np.abs(delta))),
                         int(np.count_nonzero(delta)), candidate))
    # One best proposal per displacement scale, then remaining candidates.
    chosen, used = [], set()
    for lo, hi in ((0., .03), (.03, .1), (.1, .3), (.3, 1.), (1., np.inf)):
        eligible = [j for j, p in enumerate(bank) if lo < p[2] <= hi]
        if eligible:
            j = min(eligible, key=lambda k: bank[k][0])
            chosen.append(bank[j]); used.add(j)
    chosen.extend(bank[j] for j in sorted(range(len(bank)), key=lambda j: bank[j][0])
                  if j not in used)
    return chosen[:count]


def run(checkpoint, out, seconds, candidates):
    saved = np.load(checkpoint)
    labels, logs = saved["labels"].astype(float), saved["logs"].copy()
    orientation = saved["orientation"].astype(int)
    heads, n = logs.shape
    x = ((np.arange(len(labels))[:, None] >> np.arange(n)) & 1).astype(float)
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    multisets = {o: np.sort(logs[orientation == o], axis=0) for o in (-1, 1)}
    start = time.monotonic()
    state = evaluate(t, labels, logs, saved["coefficients"])
    events, certificate, iteration = [], None, 0
    while time.monotonic()-start < seconds:
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
        bank = proposals(logs, orientation, gradient, candidates)
        if not bank:
            break
        best = None
        event = dict(iteration=iteration, original_loss=state["loss"], trials=[])
        for prediction, column, maximum_move, moved, candidate in bank:
            if time.monotonic()-start >= seconds:
                break
            fit = evaluate(t, labels, candidate, solver="lbfgs",
                           initial_score=state["score"])
            trial = dict(column=column, prediction=prediction, maximum_move=maximum_move,
                         moved=moved, loss=fit["loss"], inner_gradient=fit["inner_gradient"])
            event["trials"].append(trial)
            print(json.dumps(dict(phase="trial", iteration=iteration,
                                  seconds=time.monotonic()-start, **trial)), flush=True)
            if fit["loss"] < state["loss"]-1e-9 and (
                    best is None or fit["loss"] < best[0]["loss"]):
                best = fit, candidate
        event["accepted"] = best is not None
        if best is not None:
            state, logs = best
        for o in (-1, 1):
            assert np.array_equal(np.sort(logs[orientation == o], axis=0), multisets[o])
        events.append(event)
        print(json.dumps(dict(phase="complete", seconds=time.monotonic()-start, **event)), flush=True)
        iteration += 1
        if best is None:
            break
    np.savez(out/"checkpoint.npz", labels=labels, logs=logs,
             orientation=orientation, coefficients=state["coefficient"])
    result = dict(n=n, heads=heads, seconds=time.monotonic()-start,
                  final_loss=state["loss"], certificate=certificate, events=events,
                  scope="One finite table, fixed slope multisets, heuristic proposals.",
                  failure_is_not_a_lower_bound=True)
    (out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--candidates", type=int, default=5)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.seconds, args.candidates)
