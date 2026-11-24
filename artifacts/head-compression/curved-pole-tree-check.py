#!/usr/bin/env python3
"""Check all 256 strict tree signs using four curved poles, exactly.

Every reported pattern has an explicit rational residue witness, evaluated
again in the original eight-by-four matrix. This is a finite construction,
not a recursive interpolation theorem or an asymptotic head compiler.
"""
import importlib.util
import itertools
import json
from fractions import Fraction as F
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    "exact", Path(__file__).with_name("reverse-joint-affine-plane-search.py"))
exact = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exact)

eps = F(1, 100000)
eta = F(1, 1000)
poles = [eps*(4+a)+eps**2*(16 if h == 1 else 0)
         for h, a in enumerate((-3, -1, 1, 3))]
times = [1+4*eps+eta*a for a in (-3, -1, 1, 3, -2, 2, 0, 0)]
masks = [set(range(4))]*4+[{1, 3}, {1, 3}, {2}, {3}]
assert min(poles) > 0 and min(times) > max(poles)

results = []
for power in (1, 2):
    witnesses = {}
    per_permutation = []
    for permutation in itertools.permutations(range(4)):
        matrix = [[F(1)/(t-poles[h])**power if permutation[h] in mask else F(0)
                   for h in range(4)] for t, mask in zip(times, masks)]
        found, _ = exact.orthants(matrix, [F(0)]*8)
        per_permutation.append(len(found))
        for pattern, residues in found.items():
            scores = [sum(a*c for a, c in zip(row, residues)) for row in matrix]
            assert all(scores)
            assert pattern == sum((score > 0) << i for i, score in enumerate(scores))
            if pattern not in witnesses:
                witnesses[pattern] = {
                    "permutation": list(permutation),
                    "residues": list(map(str, residues)),
                    "scores": list(map(str, scores)),
                }
    assert set(witnesses) == set(range(256)), (power, len(witnesses))
    results.append({"power": power, "coverage": len(witnesses),
                    "per_permutation": per_permutation,
                    "witnesses": witnesses})
    print(f"Power {power}: all 256 strict patterns have checked rational witnesses.", flush=True)

output = {"poles": list(map(str, poles)), "times": list(map(str, times)),
          "masks": [sorted(mask) for mask in masks], "results": results}
Path(__file__).with_suffix(".json").write_text(json.dumps(output, indent=2)+"\n")
