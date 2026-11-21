#!/usr/bin/env python3
"""Independent rational verification of an explicitly listed input promise.

Denominators are checked on the entire Boolean cube. Labels are checked only
at the supplied vertices. This does not certify a full-cube upper bound.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


def verify(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    n, vertices, labels = data["n"], data["vertices"], data["labels"]
    assert isinstance(n, int) and n > 0
    assert vertices and len(vertices) == len(labels)
    assert len(set(vertices)) == len(vertices)
    assert all(isinstance(x, int) and 0 <= x < 1 << n for x in vertices)
    assert all(y in (-1, 1) for y in labels)
    for head in data["heads"]:
        a, b = head["numerator"], head["denominator"]
        assert len(a) == len(b) == n + 1
        assert all(isinstance(z, int) for z in a + b)
        slopes = b[1:]
        assert (all(z > 0 for z in slopes) or all(z < 0 for z in slopes)
                or all(z == 0 for z in slopes))
        assert b[0] + sum(min(z, 0) for z in slopes) > 0
    bias = Fraction(*data["bias"])
    least = None
    for vertex, label in zip(vertices, labels):
        indices = [i + 1 for i in range(n) if vertex >> i & 1]
        score = bias
        for head in data["heads"]:
            a, b = head["numerator"], head["denominator"]
            score += Fraction(a[0] + sum(a[i] for i in indices),
                              b[0] + sum(b[i] for i in indices))
        margin = label * score
        assert margin > 0, (str(path), vertex)
        least = margin if least is None else min(least, margin)
    return {"file": str(path), "sha256": hashlib.sha256(raw).hexdigest(),
            "n": n, "heads": len(data["heads"]),
            "promised_vertices_checked": len(vertices),
            "whole_cube_denominator_admissibility": True,
            "strict_promised_signs": True, "margin_approximation": float(least),
            "scope": "Explicit promised vertices only; no universal head bound."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", type=Path, nargs="+")
    args = parser.parse_args()
    for path in args.certificates:
        print(json.dumps(verify(path)), flush=True)
