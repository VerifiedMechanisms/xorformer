#!/usr/bin/env python3
"""Exact primal audit of the four-head, three-memory mixed-fiber module.

This independently constructs strictly signed outputs for every eight-bit
word. Each accepted word includes an exact rational residue witness. No
floating-point optimization or probabilistic inference is used.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path
import sympy as sp

IDENTITY = (0, 1, 2, 3)
TEMPLATES = tuple((IDENTITY, permutation) for permutation in
                  (IDENTITY, (0, 2, 3, 1), (1, 3, 0, 2)))
COMPACT_TEMPLATES = ((IDENTITY, IDENTITY),
                     ((0, 2, 1, 3), (1, 0, 3, 2)),
                     ((0, 1, 3, 2), (1, 2, 3, 0)))
MASKS = (3, 5, 6, 7)


def matrices(poles, nodes, pair):
    permutations = (IDENTITY,) + pair
    cauchy = sp.Matrix([[1 / (node - pole) for pole in poles] for node in nodes])
    basis = cauchy.nullspace()
    assert len(basis) == 2
    matrix = sp.Matrix([
        [sum(vector[permutations[j][h]] /
             (node - sum(poles[permutations[k][h]] for k in range(3) if mask >> k & 1))
             for h in range(4)) if mask >> j & 1 else sp.Rational(0)
         for j in range(3) for vector in basis]
        for mask in MASKS for node in nodes])
    dual = sp.Matrix.hstack(*matrix.T.nullspace())
    assert dual.shape == (8, 2)
    pivot_rows = matrix.T.rref()[1]
    inverse = matrix[list(pivot_rows), :].inv()
    assert matrix.T * dual == sp.zeros(6, 2)
    return matrix, basis, dual, pivot_rows, inverse


def primal_for_word(data, word):
    matrix, basis, dual, pivot_rows, inverse = data
    signs = [sp.Integer(1 if word >> i & 1 else -1) for i in range(8)]
    signed = sp.diag(*signs) * dual
    target = -sum((signed[i, :].T for i in range(8)), sp.zeros(2, 1))
    for i, j in combinations(range(8), 2):
        pair = sp.Matrix.hstack(signed[i, :].T, signed[j, :].T)
        if pair.det() == 0:
            continue
        additions = pair.inv() * target
        if any(x < 0 for x in additions):
            continue
        positive = [sp.Integer(1)] * 8
        positive[i] += additions[0]
        positive[j] += additions[1]
        output = sp.Matrix([signs[k] * positive[k] for k in range(8)])
        assert dual.T * output == sp.zeros(2, 1)
        coefficient = inverse * output[list(pivot_rows), :]
        assert matrix * coefficient == output
        assert all(signs[k] * output[k] >= 1 for k in range(8))
        residues = [basis[0] * coefficient[2 * k] + basis[1] * coefficient[2 * k + 1]
                    for k in range(3)]
        return coefficient, residues, output
    return None


def audit(poles, nodes, templates=TEMPLATES, store_witnesses=False):
    assert len(poles) == 4 and len(nodes) == 2
    assert min(nodes) > 3 * max(poles) > 0
    data = [matrices(poles, nodes, pair) for pair in templates]
    missing, witnesses, usage = [], [], [0] * len(templates)
    for word in range(256):
        for index, item in enumerate(data):
            result = primal_for_word(item, word)
            if result is None:
                continue
            coefficient, residues, output = result
            usage[index] += 1
            # Direct verification on all row/singleton and mixed fibers.
            permutations = (IDENTITY,) + templates[index]
            for node in nodes:
                for mask in range(8):
                    denominators = [node - sum(poles[permutations[k][h]]
                                    for k in range(3) if mask >> k & 1) for h in range(4)]
                    assert min(denominators) > 0
                    value = sum(sum(residues[k][permutations[k][h]]
                                    for k in range(3) if mask >> k & 1) / denominators[h]
                                for h in range(4))
                    if mask in (0, 1, 2, 4):
                        assert value == 0
                    else:
                        position = 2 * MASKS.index(mask) + nodes.index(node)
                        assert value == output[position]
            if store_witnesses:
                witnesses.append({"word": word, "template": index,
                                  "coefficients": [str(x) for x in coefficient],
                                  "outputs": [str(x) for x in output]})
            break
        else:
            missing.append(word)
    return {"poles": [str(x) for x in poles], "nodes": [str(x) for x in nodes],
            "missing": missing, "template_usage": usage,
            "minimum_denominator_lower_bound": str(min(nodes) - 3 * max(poles)),
            "witnesses": witnesses}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--compact-grid", action="store_true")
    args = parser.parse_args()
    cases = [(tuple(map(sp.Rational, (1, 2, 3, 4))),
              tuple(map(sp.Rational, (14, 13))), TEMPLATES)]
    if args.compact_grid:
        cases += [(tuple(sp.Rational(j, scale) for j in (1, 2, 3, 4)),
                   (sp.Rational(1), sp.Rational(15, 16)), COMPACT_TEMPLATES)
                  for scale in (100, 1000, 1000000)]
    reports = []
    for index, (poles, nodes, templates) in enumerate(cases):
        report = audit(poles, nodes, templates, store_witnesses=index == 0)
        reports.append(report)
        print(json.dumps({k: v for k, v in report.items() if k != "witnesses"}), flush=True)
    if args.out:
        args.out.write_text(json.dumps(reports, indent=2) + "\n")


if __name__ == "__main__":
    main()
