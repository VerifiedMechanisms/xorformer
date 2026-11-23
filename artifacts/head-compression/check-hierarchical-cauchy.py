#!/usr/bin/env python3
"""Exact finite check of the written hierarchical Cauchy decoder.

Uses only fractions.Fraction and exhausts all encoded bit assignments.
This is computational evidence for finite H, not a Lean proof or a
full-cube admissibility check. Default H=4; H=8 checks 4096 assignments.
"""
from fractions import Fraction
from itertools import product
import argparse


def queries(heads):
    result = []

    def walk(start, width, depth):
        if width == 1:
            return
        midpoint = start + width // 2
        for pair in range(width // 2):
            boundary = (2 * pair + 1) * (2 ** depth)
            result.append((start, midpoint, start + width, depth, pair, boundary))
        walk(start, width // 2, depth + 1)
        walk(midpoint, width // 2, depth + 1)

    walk(0, heads, 0)
    return result


def encode(heads, signs, descriptors):
    lookup = {(q[0], q[3], q[4]): s for q, s in zip(descriptors, signs)}

    def walk(ranks, start, depth):
        if len(ranks) == 1:
            return ranks
        left, right = [], []
        for pair in range(len(ranks) // 2):
            lower, upper = ranks[2 * pair:2 * pair + 2]
            if lookup[start, depth, pair] == 1:
                left.append(upper)
                right.append(lower)
            else:
                left.append(lower)
                right.append(upper)
        midpoint = start + len(ranks) // 2
        return walk(left, start, depth + 1) + walk(right, midpoint, depth + 1)

    return walk(list(range(1, heads + 1)), 0, 0)


def check(heads):
    assert heads >= 2 and heads & (heads - 1) == 0
    scale = 4 * heads
    poles = {j: 1 - Fraction(1, scale ** (2 * j)) for j in range(1, heads + 1)}
    descriptors = queries(heads)
    expected = (heads // 2) * (heads.bit_length() - 1)
    assert len(descriptors) == expected
    # Precompute exact kernels for each distinct query boundary.
    kernels = {}
    for boundary in {q[-1] for q in descriptors}:
        probe = 1 + Fraction(1, scale ** (2 * boundary + 1))
        kernels[boundary] = {j: 1 / (probe - poles[j]) for j in poles}
        assert all(probe > pole for pole in poles.values())
    seen = set()
    for signs in product((-1, 1), repeat=expected):
        permutation = encode(heads, signs, descriptors)
        assert sorted(permutation) == list(range(1, heads + 1))
        seen.add(tuple(permutation))
        for descriptor, desired in zip(descriptors, signs):
            start, midpoint, end, _, _, boundary = descriptor
            kernel = kernels[boundary]
            value = sum(kernel[j] for j in permutation[start:midpoint])
            value -= sum(kernel[j] for j in permutation[midpoint:end])
            assert desired * value > 0, (heads, signs, descriptor, permutation, value)
    assert len(seen) == 2 ** expected
    print(f"H={heads}: all {2 ** expected} strict patterns on {expected} queries verified exactly.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("heads", type=int, nargs="?", default=4)
    check(parser.parse_args().heads)
