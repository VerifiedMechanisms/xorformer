#!/usr/bin/env python3
"""Exact audit of binary switching and its positive reciprocal compiler."""
import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import random


def val(word):
    out = 0
    for bit in word:
        out = 2 * out + bit
    return out


def construction(r):
    records = []
    for i in range(1, r):
        for a in itertools.product((0, 1), repeat=i - 1):
            for b in itertools.product((0, 1), repeat=r - i - 1):
                lo_x = 2 * val(a) * 2 ** (r - i)
                lo_y = 2 * val(b) * 2 ** i
                records.append(((i, a, b), (lo_x, lo_x + 2 ** (r - i),
                                            lo_y, lo_y + 2 ** i)))
    assert len(records) == (r - 1) * 2 ** (r - 2)
    assert len({rect for _, rect in records}) == len(records)
    return records


def witness(r, selected):
    points = []
    for a in itertools.product((0, 1), repeat=r - 1):
        b = []
        for j in range(1, r):
            i = r - j
            sigma = 0 if selected[(i, a[:i - 1], tuple(b))] else 1
            b.append(a[i - 1] ^ sigma)
        points.append((2 * val(a) + 1, 2 * val(b) + 1))
    assert len(set(points)) == 2 ** (r - 1)
    return points


def verify(r, assignments):
    records = construction(r)
    h = 2 ** (r - 1)
    base = 16 * h
    powers = {k: Fraction(base) ** k for k in range(-2 ** r, 2 ** r + 1)}
    count = 0
    for labels in assignments:
        selected = {key: bool((labels >> j) & 1)
                    for j, (key, _) in enumerate(records)}
        points = witness(r, selected)
        for key, (a, b, c, d) in records:
            hits = sum(a < s < b and c < t < d for s, t in points)
            assert hits == int(selected[key])
            score = -Fraction(1, 2)
            for s, t in points:
                exponents = (a - s, s - b, c - t, t - d)
                u = sum(powers[k] for k in exponents)
                term = 1 / (1 + u)
                if a < s < b and c < t < d:
                    assert max(exponents) <= -1
                    assert 0 < u <= Fraction(1, 4)
                    assert term >= Fraction(4, 5)
                else:
                    assert max(exponents) >= 1
                    assert u >= 16 * h
                    assert 0 < term < Fraction(1, 16 * h)
                score += term
            assert (score if selected[key] else -score) > Fraction(1, 4)
            count += 1
    return {"r": r, "heads": h, "queries": len(records),
            "assignments": len(assignments), "exact_scores": count}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rng = random.Random(20261122)
    results = []
    for r in (3, 4, 5, 6):
        m = (r - 1) * 2 ** (r - 2)
        assignments = list(range(2 ** m)) if r <= 4 else [
            0, 2 ** m - 1, *[rng.getrandbits(m) for _ in range(32)]]
        results.append(verify(r, assignments))
    result = {"status": "PASS", "arithmetic": "fractions.Fraction",
              "scope": "finite audit supplementing the written general proof",
              "cases": results}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
