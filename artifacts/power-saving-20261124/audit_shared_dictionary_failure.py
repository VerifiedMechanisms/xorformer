"""Exact Farkas audit of one exploratory shared-dictionary obstruction.

The LP is only used to propose a sparse nonnegative dual vector. Every accepted
vector is reconstructed and checked using rational arithmetic. This certifies
failure of a particular finite dictionary, not an unrestricted head bound.
"""

import itertools
import json
from pathlib import Path

import numpy as np
import sympy as sp
from scipy.optimize import linprog


def main():
    root = Path("artifacts/power-saving-20261124")
    source = json.loads((root / "shared-pencil-n4-h4-affine.json").read_text())
    args = source["arguments"]
    rng = np.random.default_rng(args["seed"])
    n, H = args["bits"], args["heads"]
    vertices = list(itertools.product([0, 1], repeat=n))
    targets = rng.choice([-1., 1.], size=(args["samples"], len(vertices)))
    first = source["results"][0]
    index = first["first_failure_indices"][0]
    y = [sp.Integer(int(t)) for t in targets[index]]
    b = sp.Matrix(first["slopes"])
    p = [1 + sum(x[i] * 2**i for i in range(n)) for x in vertices]
    base = sp.Matrix([[1] + [sp.Rational(1, t + j + 1) for j in range(H)] + list(x)
                      for x, t in zip(vertices, p)])
    F = np.array(base, dtype=float)
    yy = np.array(y, dtype=float).reshape(-1)
    constraints = np.column_stack([-yy[:, None] * F, np.ones(len(y))])
    objective = np.zeros(F.shape[1] + 1)
    objective[-1] = -1
    records = []
    offsets = []
    for perm in itertools.permutations(range(H)):
        offset = sp.Matrix([sum(sum(b[h, i] * x[i] for i in range(n)) *
                                sp.Rational(1, t + perm[h] + 1) for h in range(H))
                            for x, t in zip(vertices, p)])
        offsets.append(offset)
        ofs = np.array(offset, dtype=float).reshape(-1)
        lp = linprog(objective, A_ub=constraints, b_ub=yy * ofs,
                     bounds=[(None, None)] * F.shape[1] + [(None, 1)], method="highs")
        if not lp.success:
            raise RuntimeError("LP did not return a dual proposal")
        support = np.flatnonzero(-lp.ineqlin.marginals > 1e-9).tolist()
        M = sp.Matrix([[y[s] * base[s, j] for s in support]
                       for j in range(base.cols)] + [[1] * len(support)])
        rhs = sp.Matrix([0] * base.cols + [1])
        solution, parameters = M.gauss_jordan_solve(rhs)
        if parameters.rows:
            raise RuntimeError("Dual support is not unique")
        assert all(t >= 0 for t in solution)
        assert M * solution == rhs
        value = sum(solution[i] * y[s] * offset[s] for i, s in enumerate(support))
        assert value <= 0, (perm, value)
        records.append({"permutation": list(perm), "support": support,
                        "dual": [str(t) for t in solution],
                        "signed_offset": str(value)})
    # The convex relaxation has full quotient dimension and its average offset
    # is zero. Hence its image contains a neighborhood of zero modulo the free
    # feature space, and every strict Boolean label is feasible in the relaxed
    # problem. The failed pure branches above give an exact integrality gap.
    assert sum(offsets, sp.zeros(len(vertices), 1)) == sp.zeros(len(vertices), 1)
    combined = base.row_join(sp.Matrix.hstack(*offsets))
    pivots = combined.rref()[1]
    assert len(pivots) == len(vertices)
    determinant = combined[:, list(pivots)].det()
    assert determinant != 0
    result = {"kind": "exact rational certificate for one fixed dictionary only",
              "bits": n, "heads": H, "target_index": index,
              "target": [int(t) for t in y], "slopes": first["slopes"],
              "records": records,
              "convex_relaxation": {
                  "sum_of_offsets_is_zero": True,
                  "feature_and_offset_rank": len(pivots),
                  "pivot_columns": list(pivots),
                  "nonzero_pivot_determinant": str(determinant),
                  "consequence": "Every strict target is feasible after convexifying the permutation branches"}}
    (root / "shared-pencil-exact-failure.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Exactly certified {len(records)} permutation branches infeasible for target {index}.")
    print("Exactly certified full relaxed quotient span and zero mean offset.")


if __name__ == "__main__":
    main()
