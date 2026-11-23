#!/usr/bin/env python3
"""Exact finite checks for butterfly-rectangle-decoder.tex.

No numerical optimization is used.  The exhaustive tests for d <= 3
check every switch setting, every rectangle count, and injectivity.
The d = 4 test checks a reproducible sample only.
"""

import itertools
import json
import random


def switches(d):
    return [(k, s, g) for k in range(d)
            for s in range(1 << k)
            for g in range(1 << (d - k - 1))]


def permutation(d, bits):
    choice = dict(zip(switches(d), bits))
    image = list(range(1 << d))
    for k in range(d):
        for i, current in enumerate(image):
            s = current & ((1 << k) - 1)
            g = current >> (k + 1)
            if choice[k, s, g]:
                image[i] ^= 1 << k
    assert sorted(image) == list(range(1 << d))
    return tuple(image)


def rectangle_count(d, pi, switch):
    k, s, g = switch
    # A: bit k is zero, bits above k equal g.
    a = [i for i in range(1 << d)
         if i >> (k + 1) == g and not i & (1 << k)]
    # B: bit k is one, bits below k equal s.
    mask = (1 << (k + 1)) - 1
    target = (1 << k) | s
    return sum((pi[i] & mask) == target for i in a)


def check(d, settings, exhaustive):
    seen = set()
    number = 0
    for bits in settings:
        pi = permutation(d, bits)
        recovered = tuple(rectangle_count(d, pi, e) for e in switches(d))
        assert recovered == tuple(bits), (d, bits, pi, recovered)
        if exhaustive:
            assert pi not in seen
            seen.add(pi)
        number += 1
    return {"d": d, "H": 1 << d, "switches": len(switches(d)),
            "settings_checked": number, "exhaustive": exhaustive,
            "all_rectangle_counts_correct": True,
            "injectivity_checked": exhaustive}


def main():
    results = [check(d, itertools.product((0, 1), repeat=len(switches(d))), True)
               for d in range(1, 4)]
    rng = random.Random(20261123)
    results.append(check(4, (tuple(rng.randrange(2) for _ in switches(4))
                             for _ in range(1000)), False))
    print(json.dumps({"tests": results}, indent=2))


if __name__ == "__main__":
    main()
