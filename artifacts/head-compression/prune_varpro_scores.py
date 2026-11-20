#!/usr/bin/env python3
"""Explore head deletion with joint reoptimization of all denominators.

Every accepted deletion is checked by the independent integer checker already
used by search_varpro_scores. Failed trials imply no lower bound. Use heavy.
"""
import argparse
import json
import os
import time
from pathlib import Path
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
from search_varpro_scores import Problem


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=28800)
    parser.add_argument("--trial-seconds", type=float, default=300)
    parser.add_argument("--target", type=int, required=True)
    parser.add_argument("--seed", type=int, default=100000)
    parser.add_argument("--score-penalty", type=float, default=1e-7)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    saved = np.load(args.checkpoint)
    labels, orientation = saved["labels"], saved["orientation"]
    n = int(np.log2(len(labels)))
    logs = saved["logs"].reshape(len(orientation), n)
    rng = np.random.default_rng(args.seed)
    start, trial = time.monotonic(), 0
    tried = set()
    while time.monotonic()-start < args.seconds and len(orientation) > args.target:
        choices = list(set(range(len(orientation))) - tried)
        if not choices:
            tried.clear()
            choices = list(range(len(orientation)))
        removed = int(rng.choice(choices))
        tried.add(removed)
        keep = np.arange(len(orientation)) != removed
        h = len(orientation)-1
        problem = Problem(n, h, args.seed+trial,
                          min(args.trial_seconds, args.seconds-(time.monotonic()-start)),
                          args.out, "pruned", score_penalty=args.score_penalty)
        problem.y = labels.copy()
        problem.orientation = orientation[keep].copy()
        problem.t = np.where(problem.orientation[None, :, None] > 0,
                             problem.x[:, None, :], 1-problem.x[:, None, :])
        problem.initial_logs = logs[keep].copy()
        result = problem.run()
        result["removed_head"] = removed
        with (args.out/"trials.jsonl").open("a") as stream:
            stream.write(json.dumps(result)+"\n")
        print(json.dumps({k:v for k,v in result.items() if k != "events"}), flush=True)
        if result["certificate"]:
            logs = problem.best_logs.reshape(h, n).copy()
            orientation = problem.orientation.copy()
            tried.clear()
            np.savez(args.out/"latest.npz", logs=logs, orientation=orientation,
                     labels=labels, coefficients=problem.best_coeff)
        trial += 1
    print(json.dumps({"final_heads": len(orientation), "target": args.target,
                      "seconds": time.monotonic()-start,
                      "scope": "One supplied truth table only."}), flush=True)


if __name__ == "__main__":
    main()
