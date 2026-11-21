#!/usr/bin/env python3
"""Independent exact check of a finite orthant span-matching certificate.

This checks only the listed matching, not maximality or an asymptotic claim.
It imports no search code. The dictionary is an integer NumPy array.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import numpy as np


def verify(path):
    raw = path.read_bytes()
    record = json.loads(raw)
    dictionary_path = path.parent / "dictionary.npy"
    dictionary_raw = dictionary_path.read_bytes()
    points = np.load(dictionary_path, allow_pickle=False)
    assert np.issubdtype(points.dtype, np.integer)
    size, k = points.shape
    assert size == record["dictionary_size"] and k == record["k"]
    mask = record["orthant_mask"]
    assert isinstance(mask, int) and 0 <= mask < 1 << k
    signs = [1 if not (mask >> i & 1) else -1 for i in range(k)]
    used = set()
    for left, right, alpha, beta_num, beta_den in record["matching"]:
        assert all(isinstance(x, int) for x in
                   (left, right, alpha, beta_num, beta_den))
        assert 0 <= left < size and 0 <= right < size and left != right
        assert left not in used and right not in used
        used.update((left, right))
        assert beta_den > 0
        beta = Fraction(beta_num, beta_den)
        assert all(signs[i] * (alpha * int(points[left, i]) +
                              beta * int(points[right, i])) > 0
                   for i in range(k))
    assert len(used) == 2 * record["matching_size"]
    return {"file": str(path), "sha256": hashlib.sha256(raw).hexdigest(),
            "dictionary_sha256": hashlib.sha256(dictionary_raw).hexdigest(),
            "k": k, "dictionary_size": size,
            "matching_size": len(used) // 2, "orthant_mask": mask,
            "exact_disjointness_and_signs": True,
            "scope": "Listed matching only; no maximality or universal theorem."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", type=Path, nargs="+")
    args = parser.parse_args()
    for path in args.certificates:
        print(json.dumps(verify(path)), flush=True)
