#!/usr/bin/env python3
"""Exact finite checks of joint-zero classification and butterfly invariants."""
from fractions import Fraction as F
from importlib.util import spec_from_file_location, module_from_spec
from itertools import permutations, product
from pathlib import Path

spec = spec_from_file_location(
    "krylov", Path(__file__).with_name("cauchy-krylov-leading-audit-check.py"))
krylov = module_from_spec(spec)
spec.loader.exec_module(krylov)


def additive_equations(poles, offsets):
    size = len(poles)
    def entry(h, k):
        row = [F(0)] * (2 * size)
        row[k] = 1 / (offsets[h] - poles[k])
        row[size + h] = row[k]
        return row
    equations = []
    for h in range(1, size):
        for k in range(1, size):
            a, b, c, d = entry(h, k), entry(h, 0), entry(0, k), entry(0, 0)
            equations.append([u - v - w + z for u, v, w, z in zip(a, b, c, d)])
    return equations


def butterfly(depth, bits):
    wires = list(range(2 ** depth))
    pos = 0
    for layer in range(depth):
        for wire in range(2 ** depth):
            if not (wire >> layer) & 1:
                other = wire ^ (1 << layer)
                if bits[pos]:
                    wires[wire], wires[other] = wires[other], wires[wire]
                pos += 1
    permutation = [0] * len(wires)
    for output, original in enumerate(wires):
        permutation[original] = output
    return permutation


def main():
    checks = 0
    for size in range(3, 8):
        poles = list(map(F, range(1, size + 1)))
        offsets = list(map(F, range(20, 20 + size)))
        assert krylov.rank(additive_equations(poles, offsets)) == 2 * size - 3
        equal = [F(20)] * size
        assert krylov.rank(additive_equations(poles, equal)) == size - 1
        quadratic = lambda x: 2 * x * x - 3 * x + 7
        residues = [quadratic(x) for x in poles]
        shifts = [-quadratic(x) for x in offsets]
        values = {sum((residues[p[h]] + shifts[h]) / (offsets[h] - poles[p[h]])
                      for h in range(size)) for p in permutations(range(size))}
        assert len(values) == 1
        checks += 1
    for depth in range(1, 4):
        for bits in product((0, 1), repeat=depth * 2 ** (depth - 1)):
            permutation = butterfly(depth, bits)
            for cut in range(depth + 1):
                pairs = {(h >> cut, permutation[h] % (2 ** cut))
                         for h in range(2 ** depth)}
                assert len(pairs) == 2 ** depth
                checks += 1
    print(f"PASS: {checks} exact classification/invariant cases; all butterfly settings through d=3")


if __name__ == "__main__":
    main()
