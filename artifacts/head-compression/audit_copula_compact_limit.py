#!/usr/bin/env python3
"""Exact audit of an arbitrarily compact four-head mixed-fiber module.

All symbolic arithmetic is over QQ[e].  The three limiting Gale planes
jointly admit all 256 strict words.  Polynomial kernel bases with independent
limits imply the same assertion for every sufficiently small positive e.
This is a finite module, not an asymptotic head-complexity theorem.
"""
import argparse
from functools import reduce
from itertools import combinations
import json
from math import gcd, lcm
from pathlib import Path

import sympy as sp
from sympy.polys.domains import QQ
from sympy.polys.matrices import DomainMatrix

E = sp.Symbol("e")
DOMAIN = QQ.poly_ring(E)
IDENTITY = (0, 1, 2, 3)
NODES = (sp.Rational(1), sp.Rational(15, 16))
MASKS = (3, 5, 6, 7)
TEMPLATES = (
    (IDENTITY, IDENTITY),
    ((0, 2, 1, 3), (1, 0, 3, 2)),
    ((0, 1, 3, 2), (1, 2, 3, 0)),
)
EXPECTED_PLANES = (
    ((43065, 0, 43065, 0, 43065, 0, -124740, 103936),
     (0, 45936, 0, 45936, 0, 45936, -126225, 102544)),
    ((200160, 0, 15076035, -16604160, -14106240, 18333696, -5866560, 5161984),
     (0, 17792, 1285875, -1415808, -1231200, 1607040, -529200, 466560)),
    ((3345, 0, -57855, 69632, 31245, -31744, -13920, 12032),
     (0, 3568, -61200, 73200, 27900, -28176, -10575, 8464)),
)


def polynomial_matrix(pair):
    permutations = (IDENTITY,) + pair
    residues = [[(E*j - 1)*(E*j - sp.Rational(15, 16))*j**k /
                 sp.prod(j-l for l in range(1, 5) if l != j)
                 for j in range(1, 5)] for k in range(2)]
    # These identities give exact zero on every singleton memory fiber.
    for node in NODES:
        for vector in residues:
            assert sp.cancel(sum(vector[j-1] / (node-E*j) for j in range(1, 5))) == 0
    rows = []
    for mask in MASKS:
        selected = [j for j in range(3) if mask >> j & 1]
        for node in NODES:
            totals = [sum(permutations[j][h] + 1 for j in selected) for h in range(4)]
            rows.append([
                sp.expand(sum(residues[k][permutations[j][h]] *
                    sp.prod(node-E*totals[g] for g in range(4) if g != h)
                    for h in range(4))) if j in selected else sp.Integer(0)
                for j in range(3) for k in range(2)])
    matrix = sp.Matrix(rows)
    # Nonzero column scalings do not change the image for small e != 0.
    for col in range(6):
        divisor = sp.gcd_list(list(matrix[:, col]))
        assert divisor != 0
        matrix[:, col] = matrix[:, col].applyfunc(lambda x: sp.cancel(x/divisor))
    return matrix


def kernel_limit(matrix):
    minors = {}

    def minor(rows):
        rows = tuple(rows)
        ordered = tuple(sorted(rows))
        if ordered not in minors:
            minors[ordered] = DomainMatrix.from_Matrix(matrix[list(ordered), :]).convert_to(DOMAIN).det().as_expr()
        inversions = sum(rows[i] > rows[j] for i in range(6) for j in range(i+1, 6))
        return (-1)**inversions * minors[ordered]

    pivots = next(rows for rows in combinations(range(8), 6) if minor(rows) != 0)
    vectors = []
    for free in (i for i in range(8) if i not in pivots):
        vector = [sp.Integer(0)] * 8
        vector[free] = minor(pivots)
        for col, row in enumerate(pivots):
            replaced = list(pivots)
            replaced[col] = free
            vector[row] = -minor(replaced)
        divisor = sp.gcd_list(vector)
        vectors.append([sp.cancel(x/divisor) for x in vector])
    a, b = vectors
    pivot = next(i for i, x in enumerate(a) if x.subs(E, 0) != 0)
    b = [sp.expand(a[pivot]*b[i] - b[pivot]*a[i]) for i in range(8)]
    divisor = sp.gcd_list(b)
    b = [sp.cancel(x/divisor) for x in b]
    kernel = sp.Matrix([a, b])
    assert all(sp.expand(x) == 0 for x in matrix.T * kernel.T)
    limit = kernel.subs(E, 0)
    assert limit.rank() == 2
    return kernel, limit, pivots, minor(pivots)


def primitive_rows(matrix):
    rows = []
    for row in matrix.rref()[0].tolist():
        denominator = lcm(*(int(x.q) for x in row))
        integers = [int(x*denominator) for x in row]
        divisor = reduce(gcd, integers)
        rows.append([x//divisor for x in integers])
    return rows


def strict_kernel_word(plane, word):
    signs = [1 if word >> i & 1 else -1 for i in range(8)]
    signed = plane * sp.diag(*signs)
    target = -signed * sp.ones(8, 1)
    for i, j in combinations(range(8), 2):
        pair = signed[:, [i, j]]
        if pair.det() == 0:
            continue
        addition = pair.inv() * target
        if any(value < 0 for value in addition):
            continue
        positive = [sp.Integer(1)] * 8
        positive[i] += addition[0]
        positive[j] += addition[1]
        witness = sp.Matrix([signs[k]*positive[k] for k in range(8)])
        assert plane*witness == sp.zeros(2, 1)
        assert all(signs[k]*witness[k] >= 1 for k in range(8))
        return witness
    return None


def audit():
    report = {"templates": [], "witnesses": []}
    planes = []
    for pair, expected in zip(TEMPLATES, EXPECTED_PLANES):
        matrix = polynomial_matrix(pair)
        kernel, limit, pivots, determinant = kernel_limit(matrix)
        primitive = primitive_rows(limit)
        assert primitive == [list(row) for row in expected]
        plane = sp.Matrix(primitive)
        planes.append(plane)
        report["templates"].append({
            "permutations": pair, "limiting_gale_plane": primitive,
            "pivot_rows": pivots,
            "nonzero_pivot_minor": str(determinant),
            "polynomial_gale_basis": [[str(x) for x in row] for row in kernel.tolist()]})
    counts = [0] * len(planes)
    for word in range(256):
        for template, plane in enumerate(planes):
            witness = strict_kernel_word(plane, word)
            if witness is not None:
                counts[template] += 1
                report["witnesses"].append({"word": word, "template": template,
                    "strict_limiting_output": [str(x) for x in witness]})
                break
        else:
            raise AssertionError(f"No strict witness for word {word}")
    report["template_usage"] = counts
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    report = audit()
    print(json.dumps({"strict_words": len(report["witnesses"]),
                      "template_usage": report["template_usage"]}))
    if args.out:
        args.out.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
