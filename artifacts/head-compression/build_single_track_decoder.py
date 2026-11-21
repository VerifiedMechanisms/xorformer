#!/usr/bin/env python3
"""Exact scalar lookup decoder from a self-dual necklace ordering.

This is a binary-address decoder, not a construction on the full input cube.
The code value is a freely supplied positive scalar. No affine encoder of an
arbitrary Boolean truth table is asserted. The eight-bit seed is independently
validated below; its second half is defined by complementation, avoiding OCR
errors in the online text of Etzion and Paterson's Example 4.
"""
import argparse
from fractions import Fraction
import json
from math import factorial, prod
from pathlib import Path


SEED = [
    "00000001", "10000001", "10000011", "11000011",
    "11000111", "11010111", "11010101", "11110101",
    "11110001", "11010001", "11011001", "01011001",
    "01011000", "01001000", "00001000", "00001001",
]


def build():
    r = 8
    s = len(SEED)
    words = [tuple(map(int, w)) + tuple(1-int(c) for c in w) for w in SEED]
    assert all(sum(a != b for a, b in zip(words[i], words[(i+1) % s])) == 2
               for i in range(s))
    orbits = [{w[i:] + w[:i] for i in range(2*r)} for w in words]
    assert all(len(o) == 2*r for o in orbits)
    assert len(set.union(*orbits)) == 1 << r
    track = [words[i][(-b) % (2*r)] for b in range(2*r) for i in range(s)]
    period = len(track)
    codes = [tuple(track[(t+j*s) % period] for j in range(r))
             for t in range(period)]
    assert len(set(codes)) == 1 << r
    # Parameters t=1,...,period and addresses j=0,...,r-1 are evaluated
    # at z=t+s*j. Roots are placed halfway between consecutive integers
    # exactly when the generating track changes sign.
    last = period + (r-1)*s
    twice_roots = [2*i+3 for i in range(last-1)
                   if track[i % period] != track[(i+1) % period]]
    degree = len(twice_roots)
    heads = degree+1
    sign_at_one = 2*track[0]-1
    leading_sign = sign_at_one * (-1)**degree
    # P(z) = leading_sign * product(2*z-root). D(z)=product(z+h).
    # Residues are P(-h)/D'(-h), with h=1,...,heads.
    residues = []
    for h in range(1, heads+1):
        numerator = leading_sign*prod(-2*h-a for a in twice_roots)
        derivative = (-1)**(h-1)*factorial(h-1)*factorial(heads-h)
        value = Fraction(numerator, derivative)
        residues.append([value.numerator, value.denominator])
    return {
        "scope": "Scalar-code lookup with three binary address bits only; no full-cube head upper bound.",
        "word_bits": r, "address_bits": 3, "shift": s,
        "code_parameters": list(range(1, period+1)),
        "labels": [[2*v-1 for v in code] for code in codes],
        "poles": list(range(1, heads+1)), "residues": residues,
        "twice_roots": twice_roots, "leading_sign": leading_sign,
        "seed_first_halves": SEED,
        "source": "https://etzion.net.technion.ac.il/files/2016/02/P36.pdf",
        "source_location": "Example 4 and Theorems 20-21; seed properties checked independently here",
        "head_count": heads,
        "track_transitions": sum(track[i] != track[(i+1) % period]
                                 for i in range(period)),
        "denominator_formula": "t + shift*sum(2^i*y_i) + pole",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    data = build()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(data, indent=2)+"\n")
    print(json.dumps({k:data[k] for k in ("word_bits", "address_bits", "head_count",
                                         "track_transitions", "scope")}))
