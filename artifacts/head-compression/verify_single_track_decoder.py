#!/usr/bin/env python3
"""Independently verify every scalar-code/address pair using exact fractions."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


def verify(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    r, k = data["word_bits"], data["address_bits"]
    assert r == 1 << k
    codes, labels = data["code_parameters"], data["labels"]
    assert len(codes) == len(labels) == 1 << r
    assert len(set(codes)) == len(codes)
    assert all(isinstance(t, int) and t > 0 for t in codes)
    assert all(len(row) == r and all(v in (-1, 1) for v in row) for row in labels)
    assert len({tuple(row) for row in labels}) == 1 << r
    poles = data["poles"]
    residues = [Fraction(*v) for v in data["residues"]]
    assert len(poles) == len(residues) == data["head_count"]
    assert all(isinstance(h, int) and h > 0 for h in poles)
    assert isinstance(data["shift"], int) and data["shift"] > 0
    minimum = None
    checked = 0
    for t, row in zip(codes, labels):
        for address, label in enumerate(row):
            bits = [(address >> i) & 1 for i in range(k)]
            z = t + sum(data["shift"]*(1 << i)*bits[i] for i in range(k))
            value = sum((a/Fraction(z+h) for a, h in zip(residues, poles)), Fraction())
            margin = label*value
            assert margin > 0, (t, address, margin)
            minimum = margin if minimum is None else min(minimum, margin)
            checked += 1
    return {"certified": True, "pairs_checked": checked,
            "distinct_words": len(labels), "word_bits": r,
            "address_bits": k, "heads": len(poles),
            "minimum_margin": [minimum.numerator, minimum.denominator],
            "sha256": hashlib.sha256(raw).hexdigest(),
            "scope": "Exact scalar-code lookup only. The scalar encoder is not supplied."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(args.certificate)))
