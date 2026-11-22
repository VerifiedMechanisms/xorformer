#!/usr/bin/env python3
"""Compare matrix-free and dense convex fits on independent finite cases."""
import argparse
import json
from pathlib import Path

from search_varpro_scores import convex_hinge_fit, la, np


def check():
    rng = np.random.default_rng(2026112202)
    records = []
    for separable in (False, True):
        q, _ = la.qr(rng.normal(size=(128, 31)), mode="economic")
        labels = (np.where(q @ rng.normal(size=31) > 0, 1., -1.)
                  if separable else rng.choice([-1., 1.], size=128))
        for penalty in (0., 1e-3):
            initial = rng.normal(size=31)*1000
            dense = convex_hinge_fit(labels[:, None]*q, initial, "newton", penalty)
            fast = convex_hinge_fit(labels[:, None]*q, initial, "newton_cg", penalty)
            gap = abs(float(dense.fun-fast.fun))
            gradient = float(np.max(np.abs(fast.jac)))
            assert gap < 1e-7, (separable, penalty, gap)
            assert gradient < 1e-7, (separable, penalty, gradient)
            if separable and penalty == 0:
                assert fast.fun < 1e-12
            records.append({"separable": separable, "penalty": penalty,
                            "objective_gap": gap, "gradient_max": gradient,
                            "dense_iterations": int(dense.nit),
                            "matrix_free_iterations": int(fast.nit),
                            "cg_steps": int(fast.cg_steps)})
    return {"cases": records,
            "scope": "Numerical optimizer checks only, not a feasibility proof."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    result = check()
    args.out.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result))
