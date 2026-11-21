#!/usr/bin/env python3
"""Independently check disjoint span witnesses stored as signed powers of two.

A witness is alpha*v + beta_sign*2**(twice/2)*w. Strict positivity
of two oppositely signed powers is decided by comparing their exponents.
No floating-point exponentiation, search imports, maximality claim, or
asymptotic extrapolation is used.
"""
import argparse
import hashlib
import json
from pathlib import Path

import numpy as np


def verify(path):
    raw = path.read_bytes()
    record = json.loads(raw)
    dictionary_path = path.parent / "dictionary.npz"
    dictionary_raw = dictionary_path.read_bytes()
    with np.load(dictionary_path, allow_pickle=False) as data:
        signs, exponents = data["signs"], data["exponents"]
    assert signs.ndim == 2 and exponents.shape == signs.shape
    assert np.issubdtype(signs.dtype, np.integer)
    assert np.issubdtype(exponents.dtype, np.integer)
    assert np.all((signs == 1) | (signs == -1))
    size, k = signs.shape
    assert size == record["dictionary_size"] and k == record["k"]
    mask = record["orthant_mask"]
    assert type(mask) is int and 0 <= mask < 1 << k
    used = set()
    for left, right, alpha, beta_sign, twice in record["matching"]:
        assert all(type(v) is int for v in (left, right, alpha, beta_sign, twice))
        assert 0 <= left < size and 0 <= right < size and left != right
        assert left not in used and right not in used
        assert alpha in (-1, 1) and beta_sign in (-1, 1)
        used.update((left, right))
        for i in range(k):
            target = 1 if not (mask >> i & 1) else -1
            a = target * alpha * int(signs[left, i])
            b = target * beta_sign * int(signs[right, i])
            ea = 2 * int(exponents[left, i])
            eb = 2 * int(exponents[right, i]) + twice
            if a == b:
                assert a == 1
            elif a == 1:
                assert ea > eb
            else:
                assert eb > ea
    assert len(used) == 2 * record["matching_size"]
    return {"file": str(path), "sha256": hashlib.sha256(raw).hexdigest(),
            "dictionary_sha256": hashlib.sha256(dictionary_raw).hexdigest(),
            "k": k, "dictionary_size": size, "matching_size": len(used) // 2,
            "orthant_mask": mask, "exact_disjointness_and_signs": True,
            "scope": "Listed finite matching only; no maximality or universal theorem."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", type=Path, nargs="+")
    args = parser.parse_args()
    for path in args.certificates:
        print(json.dumps(verify(path)), flush=True)
