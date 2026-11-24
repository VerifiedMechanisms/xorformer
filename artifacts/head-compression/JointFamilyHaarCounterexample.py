#!/usr/bin/env python3
"""Verify exact fixed-prescription Haar Farkas certificates.

Only rational arithmetic is used. This does not prove infeasibility for an
adaptive pole pool, adaptive query times, or another permutation encoding.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import importlib.util
import json

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "paired", HERE / "butterfly-paired-offset-check.py")
paired = importlib.util.module_from_spec(spec)
spec.loader.exec_module(paired)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", nargs="?", default=str(HERE / "joint-family-haar-h32-geometric-dual.json"))
    args = parser.parse_args()
    data = json.loads(Path(args.certificate).read_text())
    d, epsilon = data["d"], F(data["epsilon"])
    mode = data["mode"]
    def geometry(depth):
        gamma = [epsilon**((k+1) if mode == "geometric" else 2**k)
                 for k in range(depth)]
        poles = [sum((gamma[k] for k in range(depth) if y >> k & 1), F(0))
                 for y in range(1 << depth)]
        return gamma, poles
    paired.geometry = geometry
    rows, labels = paired.reduced_rows(d, data["bits"], "haar")
    assert labels == data["labels"]
    lam = list(map(F, data["lambda"]))
    value = paired.verify_dual(rows, lam, 1 << d)
    assert any(lam)
    switches = paired.bf.switches(d)
    assert data["bits"] == [int(bool(s & (1 << (k-1)))) if k else 0
                            for k, s, g in switches]
    gamma, poles = geometry(d)
    assert all(1-poles[s]-poles[y] > 0
               for k, s, g in switches for y in range(1 << d))
    print(json.dumps(dict(d=d, mode=mode, epsilon=str(epsilon),
                          support=sum(x > 0 for x in lam),
                          affine_sign=-1 if value < 0 else 0,
                          all_residue_coefficients_cancel=True,
                          all_scalar_denominators_positive=True)))


if __name__ == "__main__":
    main()
