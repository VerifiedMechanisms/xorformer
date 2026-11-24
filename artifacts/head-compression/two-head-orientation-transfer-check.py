#!/usr/bin/env python3
"""Exact small-cube checks for the three-head orientation transfer.

This is a finite arithmetic check, not a universality proof. The proof
and precise scope are in the accompanying TeX note.
"""
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path


def affine(a, x):
    return Q(a[0]) + sum(Q(c) * t for c, t in zip(a[1:], x))


def main():
    cases = [
        # Opposite original orientations; target orientation negative.
        ((-3, 5, -2, 7), (8, -4, 3, -5),
         (2, 1, 2, 3), (12, -1, -2, -3), (10, -1, -1, -1)),
        # Both original orientations positive; target orientation negative.
        ((2, -6, 9, -4), (-5, 7, -2, 8),
         (1, 2, 3, 4), (3, 4, 1, 2), (12, -2, -1, -2)),
        # Both original orientations negative; target orientation positive.
        ((7, -3, 2, -9), (-2, 5, -7, 6),
         (15, -2, -3, -4), (11, -1, -2, -3), (2, 1, 2, 1)),
    ]
    checks = 0
    outputs = []
    for forms in cases:
        a1, a2, b1, b2, ell = forms
        vertices = list(product((0, 1), repeat=3))
        bounds = [Q(1)]
        for x in vertices:
            A, C, B, D, L = [affine(f, x) for f in forms]
            assert B > 0 and D > 0 and L > 0
            P = A * D + C * B
            assert P != 0, (forms, x)
            bounds.append(L / (2 * max(B, D)))
            if (A + C) * B * D:
                bounds.append(L * abs(P) / (2 * abs((A + C) * B * D)))
        for h in (b1, b2):
            bounds.extend(abs(Q(l)) / (2 * abs(Q(b)))
                          for l, b in zip(ell[1:], h[1:]) if b)
        eps = min(bounds) / 2
        for b in (b1, b2):
            assert all((Q(l) - eps * Q(v)) * Q(l) > 0
                       for l, v in zip(ell[1:], b[1:]))
        for x in vertices:
            A, C, B, D, L = [affine(f, x) for f in forms]
            F = A / B + C / D
            G = A / (eps * (L - eps * D)) + C / (eps * (L - eps * B))
            G -= (A + C) / (eps * L)
            rhs = (L * (A * D + C * B) - eps * (A + C) * B * D)
            rhs /= L * (L - eps * B) * (L - eps * D)
            assert G == rhs
            assert G * F > 0
            checks += 1
        outputs.append({"epsilon": str(eps), "cube_vertices": len(vertices)})
    report = {"exact_vertex_checks": checks, "cases": outputs,
              "scope": "finite exact tests; universality is proved in the TeX note"}
    path = Path(__file__).with_suffix(".json")
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
