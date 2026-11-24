#!/usr/bin/env python3
"""Exact finite tests for reverse-mobius-interleaved-exceptions.tex.

The written proof quantifies over every admissible fractional linear
map. This test checks the counting lemma for every permitted retained
subset for 3 <= k <= 6, and tests one affine map and three pole maps
per retained subset. No numerical optimization or universality claim
is used.
"""

from fractions import Fraction as F
from itertools import combinations


def main():
    tests = 0
    minimum = None
    for k in range(3, 7):
        R = F(6)
        rows = [R ** (2 * i) for i in range(k)]
        cols = [R ** (2 * i + 1) for i in range(k)]
        for deleted_count in range(k - 2):
            for deleted in combinations(range(2 * k), deleted_count):
                deleted = set(deleted)
                u = [x for i, x in enumerate(rows) if i not in deleted]
                v = [x for j, x in enumerate(cols) if j + k not in deleted]
                assert len(u) + len(v) >= k + 3
                outer_threshold = min(max(u), max(v)) / R
                inner_threshold = max(min(u), min(v)) * R
                assert sum(x <= outer_threshold for x in u) >= 2
                assert sum(x <= outer_threshold for x in v) >= 2
                assert sum(x >= inner_threshold for x in u) >= 2
                assert sum(x >= inner_threshold for x in v) >= 2
                maps = [lambda t: t]
                for pole in (-2 * max(u), 2 * max(v)):
                    maps.append(lambda t, pole=pole: -1 / (t - pole))
                pole = (min(v) - min(u)) / 2
                maps.append(lambda t, pole=pole: 1 / (t - pole))
                for index, phi in enumerate(maps):
                    p = [phi(-x) for x in u]
                    d = [phi(x) for x in v]
                    assert max(p) < min(d)
                    left, right = min(p), max(d)
                    beta = right - left
                    budget = (sum(x - left for x in p) + sum(right - x for x in d)) / beta
                    assert budget >= F(50, 49) > 1
                    minimum = budget if minimum is None else min(minimum, budget)
                    if index != 3:
                        chosen_u = [x for x in u if x <= outer_threshold][:2]
                        chosen_v = [x for x in v if x <= outer_threshold][:2]
                        U, V = max(u), max(v)
                        quadruples = [(U, V, x, y) for x, y in zip(chosen_u, chosen_v)]
                    else:
                        chosen_u = [x for x in u if x >= inner_threshold][:2]
                        chosen_v = [x for x in v if x >= inner_threshold][:2]
                        small_u, small_v = min(u), min(v)
                        quadruples = [(x, y, small_u, small_v) for x, y in zip(chosen_u, chosen_v)]
                    for U, V, small_u, small_v in quadruples:
                        rho = (U - small_u) * (V - small_v) / ((U + small_v) * (V + small_u))
                        assert rho >= F(25, 49)
                        original_u = small_u if index != 3 else U
                        original_v = small_v if index != 3 else V
                        x = (phi(-original_u) - left) / beta
                        y = (right - phi(original_v)) / beta
                        assert 0 <= x < 1 and 0 <= y < 1 and x + y < 1
                        assert x * y / ((1 - x) * (1 - y)) == rho
                        assert x + y >= rho
                    tests += 1
    print("Verified", tests, "exact retained-set/map tests.")
    print("Smallest sampled normalized slope budget:", float(minimum))


if __name__ == "__main__":
    main()
