"""Finite falsification search for a separable positive-denominator relaxation.

This does not search attention representations or establish asymptotic bounds.
Every candidate is evaluated on an explicit positive parameter grid.
"""

import argparse
import itertools
import json
from pathlib import Path

import numpy as np


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--heads", type=int, default=2)
    ap.add_argument("--queries", type=int, default=3)
    ap.add_argument("--grid", type=int, default=31)
    ap.add_argument("--rounds", type=int, default=10000)
    ap.add_argument("--seed", type=int, default=20261122)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    levels = np.geomspace(0.001, 1000, args.grid)
    theta = np.array(list(itertools.product(levels, repeat=args.heads)))
    best = -1
    record = None
    for step in range(args.rounds):
        poles = np.exp(rng.uniform(-7, 7, (args.queries, args.heads)))
        residuals = rng.normal(size=(args.queries, args.heads)) * poles
        values = (residuals[None, :, :] / (theta[:, None, :] + poles)).sum(axis=2)
        thresholds = np.array([
            np.quantile(values[:, q], rng.uniform(0.15, 0.85))
            for q in range(args.queries)
        ])
        values -= thresholds
        masks = ((values > 0).astype(np.uint64) * (1 << np.arange(args.queries,
                  dtype=np.uint64))).sum(axis=1)
        unique, indices = np.unique(masks, return_index=True)
        count = len(unique)
        if count > best:
            best = count
            record = dict(args={k: str(v) if isinstance(v, Path) else v
                                for k, v in vars(args).items()},
                          step=step, patterns=count, total_patterns=2**args.queries,
                          poles=poles.tolist(), residuals=residuals.tolist(),
                          thresholds=thresholds.tolist(), witnesses={
                              str(int(mask)): theta[i].tolist()
                              for mask, i in zip(unique, indices)})
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(record, indent=2) + "\n")
            print(json.dumps({"step": step, "patterns": count}), flush=True)
        if best == 2**args.queries:
            break
    print(json.dumps({"finished": True, "best": best,
                      "complete_shattering": best == 2**args.queries}), flush=True)


if __name__ == "__main__":
    main()
