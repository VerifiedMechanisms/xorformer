#!/usr/bin/env python3
"""Solver-free exact checks for a stronger, finite Haar invariant.

This does not test arbitrary column-dependent residues, nor a compact limit.
The positive certificate covers all 256 H=8 tail words with one residue
vector. The negative certificate uses five H=16 words with one residue
vector, allowing separate node biases for every word.
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import itertools
import json

BASE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "paired", BASE / "butterfly-paired-offset-check.py")
paired = importlib.util.module_from_spec(spec)
spec.loader.exec_module(paired)


def main():
    positive = json.loads((BASE / "joint-family-haar-common-residue-primal.json").read_text())
    assert positive["d"] == 3 and positive["target_count"] == 256
    point = list(map(F, positive["point"]))
    assert len(point) == 9 and point[-1] > 0
    count = 0
    for tail in itertools.product((0, 1), repeat=8):
        rows, _ = paired.reduced_rows(3, [0] * 4 + list(tail), "haar")
        assert all(sum(x*y for x, y in zip(row, point)) > 0 for row in rows)
        count += 1
    print("H8: one exact residue vector satisfies", count, "routing words")

    negative = json.loads((BASE / "joint-family-haar-common-residue-dual.json").read_text())
    assert negative["d"] == 4 and len(negative["bits"]) == 5
    all_rows = []
    for bits in negative["bits"]:
        rows, labels = paired.reduced_rows(4, bits, "haar")
        all_rows.append(dict(zip(map(tuple, labels), rows)))
    sums = [F(0)] * 17
    total = F(0)
    for term in negative["support"]:
        weight = F(term["weight"])
        assert weight > 0
        row = all_rows[term["target"]][tuple(term["query"])]
        sums = [a + weight*b for a, b in zip(sums, row)]
        total += weight
    assert total == 1
    assert all(value == 0 for value in sums[:-1]) and sums[-1] <= 0
    print("H16: exact common-residue dual verified; support", len(negative["support"]),
          "; affine sign", 0 if sums[-1] == 0 else -1)


if __name__ == "__main__":
    main()
