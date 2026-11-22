"""Standalone exact verifier for dyadic affine-ratio certificates.

No floating-point arithmetic, NumPy, or optimizer code is used here.
"""

import argparse
import json
from pathlib import Path


def verify(path):
    data = json.loads(Path(path).read_text())
    weights = data["weights"]
    numerators = data["numerators"]
    orientation = data["orientation"]
    labels = data["labels"]
    assert weights and weights[0]
    h, n = len(weights), len(weights[0])
    assert len(numerators) == len(orientation) == h
    assert len(labels) == 2**n
    assert all(len(row) == n for row in weights+numerators)
    assert all(type(w) is int and w > 0 for row in weights for w in row)
    assert all(type(a) is int for row in numerators for a in row)
    assert all(o in [0,1] for o in orientation)
    assert all(y in [-1,1] for y in labels)
    assert data["sigma"] in [-1,1]
    assert type(data["parameter_bits"]) is int and data["parameter_bits"] >= 0
    assert type(data["verification_precision"]) is int and data["verification_precision"] >= 0
    scale = 2**data["parameter_bits"]
    precision = 2**data["verification_precision"]
    minimum = None
    for vertex in range(2**n):
        x = [(vertex >> i) & 1 for i in range(n)]
        lower = data["sigma"]*precision
        upper = lower
        for wh, ah, o in zip(weights,numerators,orientation):
            d = scale + sum(wh[i]*(1-x[i] if o else x[i]) for i in range(n))
            a = sum(ah[i]*x[i] for i in range(n))
            assert d > 0
            quotient, remainder = divmod(precision*a,d)
            assert 0 <= remainder < d
            lower += quotient
            upper += quotient + (1 if remainder else 0)
        margin = lower if labels[vertex] == 1 else -upper
        assert margin > 0, (path,vertex,lower,upper,labels[vertex])
        minimum = margin if minimum is None else min(minimum,margin)
    return {"file":str(path), "n":n, "heads":h,
            "checked_inputs":2**n, "status":"exact verification passed",
            "minimum_scaled_margin_lower_bound":str(minimum)}


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("certificates",type=Path,nargs="+")
    args=parser.parse_args()
    for certificate in args.certificates:
        print(json.dumps(verify(certificate)))
