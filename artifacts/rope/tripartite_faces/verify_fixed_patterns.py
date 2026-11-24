#!/usr/bin/env python3
"""Exact fixed parity-face patterns and an integer cubic completion.

No solver is used by this verifier. A successful run certifies consistency,
point counts, the integer cubic signs on all 102 prescribed inputs, and the
complete nonzero 2048-entry truth table. It does not certify a pure upper bound.
"""
import itertools
import json
from pathlib import Path


def fixed_pattern(heads):
    dimensions = [2, 3] if heads == 3 else [2, 2, 2]
    xcount = 2 * heads
    groups = []
    start = xcount
    for size in dimensions:
        groups.append(list(range(start, start + size)))
        start += size
    columns = list(itertools.product(*groups))
    assert len(columns) == xcount
    labels = {}

    def add(bits, label):
        bits = tuple(bits)
        assert bits not in labels or labels[bits] == label
        labels[bits] = label

    for i in range(xcount):
        for p, indices in enumerate(columns):
            if i == p:
                continue
            for bits in itertools.product((0, 1), repeat=heads):
                point = [0] * start
                for index, bit in zip((i,) + indices, bits):
                    point[index] = bit
                add(point, -prod(2 * bit - 1 for bit in bits))
    for indices in columns:
        for bits in itertools.product((0, 1), repeat=heads):
            point = [1] * start
            point[:xcount] = [bits[0]] * xcount
            for index, bit in zip(indices, bits[1:]):
                point[index] = bit
            add(point, prod(2 * bit - 1 for bit in bits))
    return labels


def prod(values):
    result = 1
    for value in values:
        result *= value
    return result


def evaluate(data, bits):
    spins = [2 * bit - 1 for bit in bits]
    return sum(coefficient * prod(spins[i] for i in monomial)
               for coefficient, monomial in zip(data['coefficients'], data['monomials']))


def main():
    three = fixed_pattern(3)
    four = fixed_pattern(4)
    assert len(three) == 102
    assert len(four) == 281
    data = json.loads((Path(__file__).parent / 'cubic_completion.json').read_text())
    assert all(len(m) <= 3 and len(set(m)) == len(m) for m in data['monomials'])
    margins = [label * evaluate(data, bits) for bits, label in three.items()]
    assert min(margins) > 0
    scores = [evaluate(data, bits) for bits in itertools.product((0, 1), repeat=11)]
    assert all(score % 2 == 1 for score in scores)
    truth = ''.join(str(int(score > 0)) for score in scores)
    expected = (Path(__file__).parent / 'cubic_completion_truth_table.txt').read_text().strip()
    assert truth == expected
    print('102 three-head target points and 281 four-head target points consistent')
    print('Cubic completion: full 2048-point nonzero verification; local margin', min(margins))


if __name__ == '__main__':
    main()
