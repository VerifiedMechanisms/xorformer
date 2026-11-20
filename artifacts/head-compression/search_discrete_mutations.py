#!/usr/bin/env python3
"""Explore denominator orientations and row mutations at a fixed head count.

Each mutation is followed by joint continuous optimization. Accepted exact
certificates concern only the supplied truth table. Run through heavy.
"""
import argparse
import json
import math
import os
from pathlib import Path
import time
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
from search_varpro_scores import Problem


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=32400)
    parser.add_argument("--trial-seconds", type=float, default=180)
    parser.add_argument("--seed", type=int, default=160000)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    saved = np.load(args.checkpoint)
    labels = saved["labels"].copy()
    n = int(math.log2(len(labels)))
    orientation = saved["orientation"].copy()
    h = len(orientation)
    logs = saved["logs"].reshape(h, n).copy()
    rng = np.random.default_rng(args.seed)
    deadline = time.monotonic()+args.seconds
    best_loss = current_loss = math.inf
    trial = 0
    while time.monotonic() < deadline:
        candidate_logs, candidate_orientation = logs.copy(), orientation.copy()
        mutation = "baseline"
        if trial:
            kind = int(rng.integers(4))
            j = int(rng.integers(h))
            if kind == 0:
                mutation = "orientation"
                candidate_orientation[j] *= -1
            elif kind == 1:
                mutation = "row restart"
                candidate_logs[j] = rng.normal(0, 3, n)
            elif kind == 2:
                mutation = "coordinate exchange"
                i, k = rng.choice(n, 2, replace=False)
                candidate_logs[j, [i, k]] = candidate_logs[j, [k, i]]
            else:
                mutation = "near pair"
                k = int(rng.choice([i for i in range(h) if i != j]))
                candidate_orientation[k] = candidate_orientation[j]
                candidate_logs[k] = candidate_logs[j]+rng.normal(0, .1, n)
            candidate_logs = np.clip(candidate_logs, -20, 20)
        problem = Problem(n, h, args.seed+trial,
                          min(args.trial_seconds, deadline-time.monotonic()),
                          args.out, "mutated", score_penalty=0)
        problem.y = labels.copy()
        problem.orientation = candidate_orientation
        problem.t = np.where(candidate_orientation[None, :, None] > 0,
                             problem.x[:, None, :], 1-problem.x[:, None, :])
        problem.initial_logs = candidate_logs.copy()
        result = problem.run()
        loss = float(result["best_loss"])
        temperature = .002*math.exp(-(trial % 50)/10)
        accepted = (loss <= current_loss or
                    rng.random() < math.exp(min(0., (current_loss-loss)/temperature)))
        result.update(mutation=mutation, accepted=accepted, temperature=temperature)
        with (args.out/"trials.jsonl").open("a") as stream:
            stream.write(json.dumps(result)+"\n")
        print(json.dumps({k:v for k,v in result.items() if k != "events"}), flush=True)
        if loss < best_loss:
            best_loss = loss
            best_logs = problem.best_logs.reshape(h, n).copy()
            best_orientation = candidate_orientation.copy()
            np.savez(args.out/"best.npz", logs=best_logs, orientation=best_orientation,
                     coefficients=problem.best_coeff, labels=labels)
        if accepted:
            logs = problem.best_logs.reshape(h, n).copy()
            orientation = candidate_orientation.copy()
            current_loss = loss
        if result["certificate"]:
            np.savez(args.out/"certified.npz", logs=problem.certified_logs,
                     orientation=candidate_orientation, labels=labels,
                     coefficients=problem.certified_coeff)
            break
        trial += 1
        if trial % 50 == 0:
            logs, orientation, current_loss = best_logs.copy(), best_orientation.copy(), best_loss


if __name__ == "__main__":
    main()
