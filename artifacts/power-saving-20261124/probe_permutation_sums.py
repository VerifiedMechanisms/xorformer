"""Explore equal-weight sums of permutation offsets, without claiming a theorem.

The shared dictionary is the exact failed four-bit dictionary already audited.
Run through ``heavy``. LP results are floating point; a missed target is not a
certificate, and successful finite coverage is not an asymptotic construction.
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
    ap.add_argument("--samples", type=int, default=0)
    ap.add_argument("--max-sum", type=int, default=2)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    root = Path("artifacts/power-saving-20261124")
    data = json.loads((root / "shared-pencil-exact-failure.json").read_text())
    n, H = data["bits"], data["heads"]
    b = np.array(data["slopes"], dtype=float)
    vertices = np.array(list(itertools.product([0, 1], repeat=n)))
    m = len(vertices)
    p = 1 + vertices @ (2 ** np.arange(n))
    poles = np.arange(1, H + 1)
    C = 1 / (p[:, None] + poles[None, :])
    F = np.column_stack([np.ones(m), C, vertices])
    affine = vertices @ b.T
    permutations = list(itertools.permutations(range(H)))
    offsets = np.array([(affine * C[:, perm]).sum(axis=1)
                        for perm in permutations])
    if args.samples:
        rng = np.random.default_rng(202611241010)
        targets = rng.choice([-1., 1.], size=(args.samples, m))
    else:
        targets = 2 * ((np.arange(2 ** m)[:, None] >> np.arange(m)) & 1) - 1
    remaining = list(range(len(targets)))
    started = time.monotonic()
    objective = np.zeros(F.shape[1] + 1)
    objective[-1] = -1
    rounds = []
    for k in range(1, args.max_sum + 1):
        # Repeated identical branches add no label classes by positive scaling.
        combinations = list(itertools.combinations_with_replacement(range(len(offsets)), k))
        candidates = [offsets[list(indices)].sum(axis=0) for indices in combinations]
        missed = []
        witnesses = {}
        for target_index in remaining:
            y = targets[target_index]
            constraints = np.column_stack([-y[:, None] * F, np.ones(m)])
            for branch_index, offset in enumerate(candidates):
                lp = linprog(objective, A_ub=constraints, b_ub=y * offset,
                             bounds=[(None, None)] * F.shape[1] + [(None, 1)],
                             method="highs")
                if (lp.success and lp.x[-1] > 1e-8 and
                        np.min(y * (F @ lp.x[:-1] + offset)) > 1e-8):
                    witnesses[str(target_index)] = list(combinations[branch_index])
                    break
            else:
                missed.append(target_index)
        item = {"sum_terms": k, "candidates": len(candidates),
                "targets_examined": len(remaining), "targets_missed": len(missed),
                "first_missed_targets": [targets[i].tolist() for i in missed[:10]],
                "first_missed_indices": missed[:10],
                "elapsed_seconds": time.monotonic() - started}
        rounds.append(item)
        print(json.dumps(item), flush=True)
        remaining = missed
        if not remaining:
            break
    result = {"kind": "floating-point finite exploration, not an asymptotic result",
              "arguments": vars(args), "target_count": len(targets),
              "rounds": rounds, "elapsed_seconds": time.monotonic() - started}
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
