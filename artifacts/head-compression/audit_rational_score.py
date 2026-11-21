#!/usr/bin/env python3
"""Independent integer-interval audit of an affine-fraction cube score.

This reports certified correct and incorrect margins against the supplied
labels. It checks admissibility on the whole cube, including constant
denominators allowed by the manuscript's strict-sign normal form. It imports
no search code. A failed margin is not a head-complexity lower bound.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import time

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def audit(path, bits):
    raw = path.read_bytes()
    data = json.loads(raw)
    n, labels, heads = data["n"], data["labels"], data["heads"]
    assert isinstance(n, int) and n > 0 and bits > 0
    count, scale = 1 << n, 1 << bits
    assert len(labels) == count and all(y in (-1, 1) for y in labels)
    for head in heads:
        a, b = head["numerator"], head["denominator"]
        assert len(a) == len(b) == n+1
        assert all(type(v) is int for v in a+b)
        assert (all(v > 0 for v in b[1:]) or all(v < 0 for v in b[1:])
                or all(v == 0 for v in b[1:]))
        assert b[0]+sum(min(v, 0) for v in b[1:]) > 0
    bias = Fraction(*data["bias"])
    lower = [scale*bias.numerator//bias.denominator]*count
    start = time.monotonic()
    for h, head in enumerate(heads):
        a, b = head["numerator"], head["denominator"]
        numerator, denominator, previous = a[0], b[0], 0
        for address in range(count):
            vertex = address^(address >> 1)
            if address:
                bit = (vertex^previous).bit_length()-1
                sign = 1 if (vertex >> bit) & 1 else -1
                numerator += sign*a[bit+1]
                denominator += sign*b[bit+1]
            assert denominator > 0
            lower[vertex] += scale*numerator//denominator
            previous = vertex
        if (h+1) % 50 == 0:
            print(json.dumps({"heads_audited": h+1,
                              "seconds": time.monotonic()-start}), flush=True)
    upper = [v+len(heads)+1 for v in lower]
    signed_lower = [lo if y > 0 else -hi for y, lo, hi in zip(labels, lower, upper)]
    signed_upper = [hi if y > 0 else -lo for y, lo, hi in zip(labels, lower, upper)]
    positive = [i for i, lo in enumerate(signed_lower) if lo > 0]
    negative = [i for i, hi in enumerate(signed_upper) if hi < 0]
    unresolved = [i for i, (lo, hi) in enumerate(zip(signed_lower, signed_upper))
                  if lo <= 0 <= hi]
    assert len(positive)+len(negative)+len(unresolved) == count
    return {"input_file": str(path), "input_sha256": hashlib.sha256(raw).hexdigest(),
            "n": n, "heads": len(heads), "vertices_checked": count,
            "precision_bits": bits, "whole_cube_denominator_admissibility": True,
            "positive_margins_certified": len(positive),
            "negative_margins_certified": len(negative),
            "unseparated_margins": len(unresolved),
            "negative_vertices": negative, "unseparated_vertices": unresolved,
            "minimum_margin_interval_numerators": [min(signed_lower), min(signed_upper)],
            "interval_denominator": scale,
            "minimum_margin_approximation": float(Fraction(min(signed_lower), scale)),
            "all_target_signs_certified": len(positive) == count,
            "seconds": time.monotonic()-start,
            "scope": "This supplied rational score and truth table only. No universal bound.",
            "failure_is_not_a_lower_bound": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path)
    parser.add_argument("--bits", type=int, default=224)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--require-correct", action="store_true")
    args = parser.parse_args()
    result = audit(args.path, args.bits)
    args.out.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("negative_vertices", "unseparated_vertices")}), flush=True)
    if args.require_correct:
        assert result["all_target_signs_certified"]
