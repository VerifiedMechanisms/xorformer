#!/usr/bin/env python3
"""Exact finite check for the sign/indicator-approximation separation.

For q=5, coordinates are the ten edges of K_q.  S contains the empty
and full edge sets, all vertex stars, and their complements.  The script
constructs a two-head strict sign score and checks the covering and
distance hypotheses of the separate indicator-error theorem.
It does not certify any universal head-complexity upper bound.
"""
from fractions import Fraction
from itertools import combinations
import json
import math
from pathlib import Path

import sympy as sp


def construct(q=5):
    edges = list(combinations(range(q), 2))
    n = len(edges)
    assert n <= 20, "The exhaustive diagnostic is intentionally small."
    full = (1 << n) - 1
    stars = [sum(1 << j for j, edge in enumerate(edges) if v in edge)
             for v in range(q)]
    selected = {0, full, *stars, *(full ^ s for s in stars)}
    incidence = sp.Matrix([[int(v in e) for e in edges] for v in range(q)])
    basis = []
    for vector in incidence.nullspace():
        common = math.lcm(*(int(v.q) for v in vector))
        row = [int(v*common) for v in vector]
        divisor = math.gcd(*row)
        basis.append([v//divisor for v in row])
    bound = max(sum(map(abs, row)) for row in basis)
    base = 2*bound+1
    normal = [sum(base**j*row[i] for j, row in enumerate(basis))
              for i in range(n)]
    zeros = {x for x in range(1 << n)
             if sum(normal[i] for i in range(n) if x >> i & 1) == 0}
    assert zeros == selected
    minimum_distance = min((x ^ y).bit_count() for x, y in combinations(selected, 2))
    assert minimum_distance >= 4
    for i, j in combinations(range(n), 2):
        patterns = {((x >> i) & 1, (x >> j) & 1) for x in selected}
        assert len(patterns) == 4
    b = [1]+[1+abs(a) for a in normal]
    bplus = [1]+[v+a for v, a in zip(b[1:], normal)]
    bmax = sum(b)
    product_bound = bmax*(bmax+sum(map(abs, normal)))
    margin = Fraction(1, 2*product_bound)
    certificate = {
        "n": n, "labels": [1 if x in selected else -1 for x in range(1 << n)],
        "bias": [margin.numerator, margin.denominator],
        "heads": [{"numerator": [0]+[-a for a in normal], "denominator": b},
                  {"numerator": [0]+normal, "denominator": bplus}],
        "construction": "Affine equality for stars, complements, and constants on K_q edges.",
        "scope": "One explicit finite sign table. Not a universal bound."
    }
    diagnostic = {
        "q": q, "n": n, "selected_vertices": sorted(selected),
        "size": len(selected), "minimum_distance": minimum_distance,
        "covering_strength_checked": 2,
        "all_cube_zero_set_checked": True,
        "integer_normal": normal, "normal_basis": basis, "encoding_base": base,
        "two_head_margin_lower_bound": [margin.numerator, margin.denominator],
        "two_head_indicator_error_lower_bound": [1, 1+7*len(selected)],
        "scope": "Exact construction and finite combinatorial hypotheses; the approximation lower bound uses the separately proved covering-set theorem."
    }
    return certificate, diagnostic


if __name__ == "__main__":
    root = Path(__file__).resolve().parent
    certificate, diagnostic = construct()
    cert_path = root/"certificates/star-level-n10-h2.json"
    cert_path.write_text(json.dumps(certificate, indent=2)+"\n")
    (root/"diagnostics/star-indicator-separation.json").write_text(
        json.dumps(diagnostic, indent=2)+"\n")
    print(json.dumps(diagnostic), flush=True)
