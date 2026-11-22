#!/usr/bin/env python3
"""Dyadically round a finite certificate with a proved uniform error bound.

Normalize each denominator to minimum one on the cube. If each normalized
coefficient changes by at most 1/(2*2^k), put e=(n+1)/(2*2^k).
The score error is at most e/(1-e) times sum_h(1+ceil(||A_h||_1)).
The script chooses k so this is below one quarter of the audited margin,
preserves strict slope signs, and independently checks the final integers.
Use heavy for large input certificates.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
from audit_rational_score import audit


def rounded_ratio(value, denominator, scale):
    return (2*value*scale+denominator)//(2*denominator)


def compress(source, source_audit, destination, audit_destination):
    raw = source.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    original = json.loads(raw)
    checked = json.loads(source_audit.read_text())
    assert checked["input_sha256"] == digest
    assert checked["all_target_signs_certified"]
    assert checked["whole_cube_denominator_admissibility"]
    n, heads = original["n"], original["heads"]
    gamma = Fraction(checked["minimum_margin_interval_numerators"][0],
                     checked["interval_denominator"])
    assert gamma > 0
    minima, amplitude = [], len(heads)
    for head in heads:
        aa, bb = head["numerator"], head["denominator"]
        assert len(aa) == len(bb) == n+1
        minimum = bb[0]+sum(min(z, 0) for z in bb[1:])
        assert minimum > 0
        assert all(z > 0 for z in bb[1:]) or all(z < 0 for z in bb[1:]) or all(z == 0 for z in bb[1:])
        minima.append(minimum)
        amplitude += (sum(map(abs, aa))+minimum-1)//minimum
    bits = 64
    while True:
        scale = 1 << bits
        assert 2*scale > n+1
        error = Fraction((n+1)*amplitude, 2*scale-(n+1))
        if 4*error >= gamma:
            bits += 16
            continue
        rounded = []
        sign_ok = True
        for head, minimum in zip(heads, minima):
            aa, bb = [[rounded_ratio(z, minimum, scale) for z in head[key]]
                       for key in ("numerator", "denominator")]
            if any(old*new <= 0 for old, new in zip(head["denominator"][1:], bb[1:]) if old):
                sign_ok = False
                break
            assert bb[0]+sum(min(z, 0) for z in bb[1:]) > 0
            rounded.append({"numerator": aa, "denominator": bb})
        if sign_ok:
            break
        bits += 16
    result = {"n": n, "labels": original["labels"], "heads": rounded,
              "bias": original["bias"], "scope": "This finite truth table only; no universal bound.",
              "dyadic_compression": {"source_sha256": digest, "fractional_bits": bits,
                 "normalized_numerator_bound_plus_heads": amplitude,
                 "uniform_score_error_upper_bound": [error.numerator, error.denominator],
                 "source_margin_lower_bound": [gamma.numerator, gamma.denominator],
                 "derived_margin_lower_bound": [(gamma-error).numerator, (gamma-error).denominator],
                 "strict_slope_signs_preserved": True}}
    destination.write_text(json.dumps(result)+"\n")
    report = audit(destination, 224)
    audit_destination.write_text(json.dumps(report, indent=2)+"\n")
    assert report["all_target_signs_certified"], report
    assert report["whole_cube_denominator_admissibility"]
    summary = {"n": n, "heads": len(heads), "fractional_bits": bits,
               "source_bytes": len(raw), "compressed_bytes": destination.stat().st_size,
               "source_sha256": digest, "compressed_sha256": report["input_sha256"],
               "uniform_error_upper_bound_approximation": float(error),
               "audited_margin_lower_approximation": report["minimum_margin_approximation"],
               "scope": result["scope"]}
    print(json.dumps(summary), flush=True)
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("source_audit", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--audit-out", type=Path, required=True)
    args = parser.parse_args()
    compress(args.source, args.source_audit, args.out, args.audit_out)
