#!/usr/bin/env python3
"""Check a finite score certificate using exact Fraction arithmetic.

This checker imports no search code. Its conclusions concern only the supplied
truth table. Run large certificates through the shared heavy command.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def verify(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    n = data["n"]
    assert isinstance(n, int) and n > 0
    labels = data["labels"]
    assert len(labels) == 1 << n and all(y in (-1, 1) for y in labels)
    heads = data["heads"]
    for head in heads:
        a, b = head["numerator"], head["denominator"]
        assert len(a) == len(b) == n + 1
        assert all(isinstance(z, int) for z in a + b)
        slopes = b[1:]
        assert (all(z > 0 for z in slopes) or all(z < 0 for z in slopes)
                or all(z == 0 for z in slopes))
        assert b[0] + sum(min(z, 0) for z in slopes) > 0
    bias = Fraction(*data["bias"])
    least = None
    for vertex, label in enumerate(labels):
        indices = [i + 1 for i in range(n) if (vertex >> i) & 1]
        score = bias
        for head in heads:
            a, b = head["numerator"], head["denominator"]
            numerator = a[0] + sum(a[i] for i in indices)
            denominator = b[0] + sum(b[i] for i in indices)
            assert denominator > 0
            score += Fraction(numerator, denominator)
        margin = label * score
        assert margin > 0, (path.name, vertex)
        least = margin if least is None else min(least, margin)
    return {"file": str(path), "sha256": hashlib.sha256(raw).hexdigest(),
            "n": n, "heads": len(heads), "vertices_checked": len(labels),
            "strict_signs_and_admissibility": True,
            "margin_approximation": float(least),
            "scope": "This finite truth table only; not a universal bound."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", type=Path, nargs="+")
    args = parser.parse_args()
    for certificate in args.certificates:
        print(json.dumps(verify(certificate)), flush=True)
