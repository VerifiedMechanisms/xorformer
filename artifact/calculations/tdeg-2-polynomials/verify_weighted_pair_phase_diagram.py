#!/usr/bin/env python3
"""Exact audits for weighted paired-product thresholds, using stdlib only.

The chamber proof and rank obstruction are analytic in the companion note.
The bounded integer grid is a regression check, not a proof of chamber coverage.
The archived certificates prove upper bounds by exhaustive integer evaluation.
"""

from fractions import Fraction
from itertools import combinations_with_replacement, product
import json
from math import prod
from pathlib import Path
from random import Random


HERE = Path(__file__).resolve().parent
ARCHIVE = HERE / "weighted_pair_head_certificates.json"
SIGNS4 = tuple(product((-1, 1), repeat=4))


def sign(value):
    assert value != 0, "This audit is for strict sign representations."
    return 1 if value > 0 else -1


def target(weights, pair_products):
    return sign(sum(a * z for a, z in zip(weights, pair_products)))


def chamber(weights):
    a, b, c, d = weights
    assert a >= b >= c >= d >= 0
    if a > b + c + d:
        return "dominant_pair"
    if a + d < b + c:
        return "majority_three"
    assert a < b + c + d and a + d > b + c
    return "essential_four"


def pivotal_indices(weights):
    result = []
    for i, weight in enumerate(weights):
        rest = weights[:i] + weights[i + 1 :]
        if any(abs(sum(a * z for a, z in zip(rest, signs))) < abs(weight)
               for signs in product((-1, 1), repeat=len(rest))):
            result.append(i)
    return result


def audit_chambers():
    counts = dict.fromkeys(("dominant_pair", "majority_three", "essential_four"), 0)
    signed_tables = set()
    for increasing in combinations_with_replacement(range(13), 4):
        weights = tuple(reversed(increasing))
        values = [sum(a * z for a, z in zip(weights, signs)) for signs in SIGNS4]
        if 0 in values:
            continue
        kind = chamber(weights)
        counts[kind] += 1
        expected_pivotal = {"dominant_pair": 1, "majority_three": 3,
                            "essential_four": 4}[kind]
        assert len(pivotal_indices(weights)) == expected_pivotal
        representative = {"dominant_pair": (1, 0, 0, 0),
                          "majority_three": (1, 1, 1, 0),
                          "essential_four": (2, 1, 1, 1)}[kind]
        for orientations in SIGNS4:
            signed = tuple(a * e for a, e in zip(weights, orientations))
            canonical = tuple(a * e for a, e in zip(representative, orientations))
            actual = tuple(target(signed, signs) for signs in SIGNS4)
            expected = tuple(target(canonical, signs) for signs in SIGNS4)
            assert actual == expected
            signed_tables.add(actual)
    print("sorted nonvanishing integer grid, weights 0..12:", counts)
    print("signed tables in this sorted grid:", len(signed_tables))


def audit_weighted_antipodal_identity():
    # Independent exact arithmetic regression for the rank-three reduction.
    rng = Random(20260916)
    checks = 0
    for _ in range(8):
        bc = [rng.randint(-4, 4) for _ in range(8)]
        dc = [rng.randint(-4, 4) for _ in range(8)]
        uc = [rng.randint(-4, 4) for _ in range(8)]
        vc = [rng.randint(-4, 4) for _ in range(8)]
        t = rng.randint(-4, 4)
        for z in product((-1, 1), repeat=8):
            b = Fraction(sum(a * v for a, v in zip(bc, z)), 1 + sum(map(abs, bc)))
            d = Fraction(sum(a * v for a, v in zip(dc, z)), 1 + sum(map(abs, dc)))
            u = sum(a * v for a, v in zip(uc, z))
            v = sum(a * w for a, w in zip(vc, z))
            p = t * (1 + b) * (1 + d) + u * (1 + d) + v * (1 + b)
            pm = t * (1 - b) * (1 - d) - u * (1 - d) - v * (1 - b)
            assert ((1 - b) * p + (1 + b) * pm) / 2 == t * (1 - b * b) + u * (d - b)
            checks += 1
    print("exact weighted-antipodal identity checks:", checks)


def audit_certificates():
    payload = json.loads(ARCHIVE.read_text())
    certificates = payload["certificates"]
    expected_keys = {f"k4_negative{i}" for i in range(4)} | {f"k3_negative{i}" for i in range(2)}
    assert set(certificates) == expected_keys
    total_vertices = 0
    for key in sorted(certificates):
        cert = certificates[key]
        k, heads = cert["pairs"], cert["heads"]
        assert heads == (3 if k == 4 else 2)
        weights = cert["weights"]
        negatives = int(key[-1])
        assert weights == ([2] if k == 4 else [1]) + [1] * (k - 1 - negatives) + [-1] * negatives
        denominators, numerators = cert["denominators"], cert["numerators"]
        assert len(denominators) == len(numerators) == heads
        for row in denominators + numerators:
            assert len(row) == 2 * k + 1 and all(type(value) is int for value in row)
        for denominator in denominators:
            slopes = denominator[1:]
            assert all(v > 0 for v in slopes) or all(v < 0 for v in slopes)
            assert denominator[0] + sum(min(0, v) for v in slopes) > 0
        if k == 3:
            construction = cert["construction"]
            scale, t, factor = (construction[name] for name in ("scale", "t", "K"))
            bc, uc, vc = (construction[name] for name in ("B", "U", "V"))
            assert t == 1 and min(bc) > 0 and sum(bc) < scale
            shifted = [factor * b + v for b, v in zip(bc, vc)]
            assert min(shifted) > 0 and sum(shifted) < factor * scale
        signed_scores = []
        for bits in product((0, 1), repeat=2 * k):
            point = (1,) + bits
            ds = [sum(a * z for a, z in zip(row, point)) for row in denominators]
            ns = [sum(a * z for a, z in zip(row, point)) for row in numerators]
            assert all(value > 0 for value in ds)
            cleared = sum(ns[h] * prod(ds[j] for j in range(heads) if j != h)
                          for h in range(heads))
            if k == 3:
                z = tuple(1 - 2 * bit for bit in bits)
                quadratic = t * (scale ** 2 - sum(b * x for b, x in zip(bc, z)) ** 2)
                quadratic += sum(u * x for u, x in zip(uc, z)) * sum(v * x for v, x in zip(vc, z))
                assert cleared == factor * quadratic
            pair_products = tuple((1 - 2 * bits[i]) * (1 - 2 * bits[k + i]) for i in range(k))
            signed_scores.append(target(weights, pair_products) * cleared)
        margin = min(signed_scores)
        assert margin == cert["minimum_signed_cleared_score"] > 0
        if k == 3:
            assert margin == factor * construction["minimum_signed_quadratic_score"]
        total_vertices += len(signed_scores)
        print(f"{key}: {len(signed_scores)} vertices, exact cleared margin {margin}")
    print("certificate vertices checked:", total_vertices)


def main():
    audit_chambers()
    audit_weighted_antipodal_identity()
    audit_certificates()
    print("verified: dominant-pair H*=2; essential-four H*=3; majority-three H*=2")
    print("This classification excludes signed-sum ties.")


if __name__ == "__main__":
    main()
