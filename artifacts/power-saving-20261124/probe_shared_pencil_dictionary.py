"""Finite experiment, not a universality proof.

For a fixed positive statistic and fixed affine numerator slopes, permute a
fixed list of positive intercepts among heads. Each branch then permits free
constant numerators and a free bias. Test which Boolean labels can be separated.
The objective probes the shared-slope exponential-patch construction idea.
Run larger instances through the shared-machine ``heavy`` launcher.
"""

import argparse
import itertools
import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bits", type=int, default=3)
    ap.add_argument("--heads", type=int, default=3)
    ap.add_argument("--dictionaries", type=int, default=5)
    ap.add_argument("--samples", type=int, default=0)
    ap.add_argument("--affine-correction", action="store_true")
    ap.add_argument("--center-slopes", action="store_true")
    ap.add_argument("--seed", type=int, default=20261124)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    vertices = np.array(list(itertools.product([0., 1.], repeat=args.bits)))
    count = len(vertices)
    if args.samples:
        targets = rng.choice([-1., 1.], size=(args.samples, count))
    else:
        if count > 16:
            raise ValueError("Exhaustive target generation limited to 16 inputs")
        targets = np.array(list(itertools.product([-1., 1.], repeat=count)))
    # All denominator constants and slopes are strictly positive.
    statistic = 1 + vertices @ (2. ** np.arange(args.bits))
    poles = np.arange(1., args.heads + 1)
    base = 1. / (statistic[:, None] + poles[None, :])
    features = np.column_stack([np.ones(count), base])
    if args.affine_correction:
        features = np.column_stack([features, vertices])
    permutations = list(itertools.permutations(range(args.heads)))
    # The free numerator column space is independent of the pole permutation.
    starts = time.monotonic()
    results = []
    for dictionary in range(args.dictionaries):
        slopes = rng.integers(-8, 9, size=(args.heads, args.bits))
        if args.center_slopes:
            slopes = args.heads * slopes - slopes.sum(axis=0, keepdims=True)
        affine = vertices @ slopes.T
        offsets = np.array([(affine * base[:, perm]).sum(axis=1)
                            for perm in permutations])
        failures = []
        branch_histogram = [0] * len(permutations)
        for idx, y in enumerate(targets):
            success = False
            constraints = np.column_stack([-y[:, None] * features, np.ones(count)])
            for j, offset in enumerate(offsets):
                objective = np.zeros(features.shape[1] + 1)
                objective[-1] = -1
                result = linprog(objective, A_ub=constraints,
                                 b_ub=y * offset,
                                 bounds=[(None, None)] * features.shape[1] + [(None, 1)],
                                 method="highs")
                if (result.success and result.x[-1] > 1e-8 and
                        np.min(y * (features @ result.x[:-1] + offset)) > 1e-8):
                    branch_histogram[j] += 1
                    success = True
                    break
            if not success:
                failures.append(idx)
        item = {"dictionary": dictionary, "slopes": slopes.tolist(),
                "target_count": len(targets), "failure_count": len(failures),
                "first_failure_indices": failures[:20],
                "successful_first_branch_histogram": branch_histogram}
        results.append(item)
        print(json.dumps({k: v for k, v in item.items()
                          if k not in ("slopes", "successful_first_branch_histogram")}),
              flush=True)
    data = {"kind": "floating-point feasibility exploration only",
            "arguments": vars(args), "elapsed_seconds": time.monotonic() - starts,
            "results": results}
    Path(args.output).write_text(json.dumps(data, indent=2) + "\n")


if __name__ == "__main__":
    main()
