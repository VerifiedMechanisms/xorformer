#!/usr/bin/env python3
"""Independently verify a promised-grid Cauchy certificate using rationals."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


def verify(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    a = [Fraction(*v) for v in data["a"]]
    b = [Fraction(*v) for v in data["b"]]
    labels, sigma = data["labels"], data["sigma"]
    assert labels and labels[0]
    m, k, h = len(labels), len(labels[0]), len(a)
    assert len(b) == len(sigma) == h
    assert all(len(row) == k for row in labels+sigma)
    assert all(v in (-1,1) for row in labels+sigma for v in row)
    assert all(v > 0 for v in b)
    margins = []
    for p in range(1,m+1):
        for j in range(k):
            value = sum((4*a[t]*b[t]*sigma[t][j]/(p+b[t])**2
                         for t in range(h)),Fraction(0))
            margin = labels[p-1][j]*value
            assert margin > 0, (p,j,margin)
            margins.append(margin)
    minimum = min(margins)
    assert minimum == Fraction(*data["margin"])
    return {"path":str(path),"sha256":hashlib.sha256(raw).hexdigest(),
            "addresses":m,"output_bits":k,"poles":h,
            "minimum_margin_approx":float(minimum),"certified":True,
            "scope":"Promised grid only. No full-cube or universal claim."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths",type=Path,nargs="+")
    args = parser.parse_args()
    for path in args.paths:
        print(json.dumps(verify(path)),flush=True)
