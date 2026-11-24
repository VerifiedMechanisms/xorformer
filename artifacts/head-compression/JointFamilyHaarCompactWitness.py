#!/usr/bin/env python3
"""Verify one compact H32 Haar witness using only exact rational arithmetic.

This is finite evidence, not a universal decoder theorem or an epsilon-to-zero
certificate. No LP solver or third-party numerical package is required.
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import json

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "paired", HERE / "butterfly-paired-offset-check.py")
paired = importlib.util.module_from_spec(spec)
spec.loader.exec_module(paired)


def main():
    data = json.loads((HERE / "joint-family-haar-h32-compact-primal.json").read_text())
    assert data["mode"] == "original" and F(data["epsilon"]) == F(1, 100)
    d = data["d"]
    H = 1 << d
    bits = data["bits"]
    switches = paired.bf.switches(d)
    assert bits == [int(bool(s & (1 << (k - 1)))) if k else 0
                    for k, s, g in switches]
    point = list(map(F, data["point"]))
    assert len(point) == H + 1 and point[-1] > 0
    residues = [a / point[-1] for a in point[:-1]]
    rows, _ = paired.reduced_rows(d, bits, "haar")
    assert all(sum((a * b for a, b in zip(row, point)), F(0)) > 0
               for row in rows)
    gamma, poles = paired.geometry(d)
    permutation = paired.bf.permutation(d, bits)
    inverse = [permutation.index(y) for y in range(H)]
    values = []
    for k, s, g in switches:
        D = 1 - poles[s]
        assert all(D - p > 0 and D + gamma[k] - p > 0 for p in poles)
        values.append(gamma[k] * sum((
            paired.mask(inverse[y], k, g, "haar") * (
                residues[y] / ((D - poles[y]) * (D + gamma[k] - poles[y]))
                + 1 / (D - poles[y]) + 1 / (D + gamma[k] - poles[y]))
            for y in range(H)), F(0)))
    biases = {}
    for k, g in dict.fromkeys((k, g) for k, s, g in switches):
        pos = [values[e] for e, (l, s, h) in enumerate(switches)
               if (l, h) == (k, g) and bits[e] == 0]
        neg = [values[e] for e, (l, s, h) in enumerate(switches)
               if (l, h) == (k, g) and bits[e] == 1]
        if pos and neg:
            assert min(pos) > max(neg)
            biases[k, g] = -(min(pos) + max(neg)) / 2
        elif pos:
            biases[k, g] = 1 - min(pos)
        else:
            biases[k, g] = -1 - max(neg)
    margins = [(1 - 2 * bits[e]) * (values[e] + biases[k, g])
               for e, (k, s, g) in enumerate(switches)]
    assert all(m > 0 for m in margins)
    assert 99 * sum(gamma) < 1
    print(json.dumps(dict(d=d, heads_in_permutation_bank=H,
                          switch_signs_verified=len(margins),
                          reduced_strict_inequalities=len(rows),
                          block_biases=len(biases),
                          epsilon=data["epsilon"],
                          all_scalar_denominators_positive=True,
                          geometric_counterexample_target=True)))


if __name__ == "__main__":
    main()
