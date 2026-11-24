#!/usr/bin/env python3
"""Exact audit of the four-head, eight-mixed-fiber copula construction.

Only Python's standard library is used. Every arithmetic operation relevant to
the certificate is over fractions.Fraction. No numerical optimizer is used.
Run with --write-certificates to replace the adjacent rational witness JSON;
without that flag the existing witnesses are checked independently of search.
The construction and its limited scope are stated in continuation-copula-trades.tex.
"""

from fractions import Fraction as Q
from itertools import combinations, product
import argparse
import json
from pathlib import Path


POLES = (1, 2, 3, 4)
NODES = (14, 13)
MASKS = (3, 5, 6, 7)
BASIS = ((Q(78, 55), Q(-12, 5), Q(1), Q(0)),
         (Q(52, 15), Q(-22, 5), Q(0), Q(1)))
IDENTITY = (0, 1, 2, 3)
TEMPLATES = (IDENTITY, (0, 2, 3, 1), (1, 3, 0, 2))
DUALS = (
    ((7800, -5145, 7800, -5145, 7800, -5145, 104, 0),
     (73515, -46893, 73515, -46893, 73515, -46893, 0, 245)),
    ((-23763535640, 13363204687, 392916888, -649638080,
      392916888, -649638080, 182752752, 0),
     (-354276520, 198807917, 12053496, -13877864,
      12053496, -13877864, 0, 1554020)),
    ((-26477449440, 14438550798, 5117626150, -4486674465,
      5117626150, -4486674465, 254650305, 0),
     (-6983755064, 3827948061, 1352121680, -1148377230,
      1352121680, -1148377230, 0, 29102892)),
)
FORBIDDEN_REPS = (
    (42, 64, 65, 66, 68, 69, 72, 74, 80, 81, 84, 85, 96, 98, 104, 106),
    (41, 66, 70, 74, 82, 86, 98, 105, 106, 107),
    (41, 64, 65, 68, 73, 80, 84, 86, 97, 105),
)
CERT_PATH = Path(__file__).with_name("copula-eight-fibers-certificates.json")


def inverse(matrix):
    """Exact Gauss-Jordan inverse, or None for a singular square matrix."""
    n = len(matrix)
    a = [[Q(v) for v in row] + [Q(i == j) for j in range(n)]
         for i, row in enumerate(matrix)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return None
        a[j], a[pivot] = a[pivot], a[j]
        scale = a[j][j]
        a[j] = [v / scale for v in a[j]]
        for i in range(n):
            if i != j:
                scale = a[i][j]
                a[i] = [x - scale * y for x, y in zip(a[i], a[j])]
    return [row[n:] for row in a]


def matvec(matrix, vector):
    return [sum((a * b for a, b in zip(row, vector)), Q(0)) for row in matrix]


def matrix(template):
    permutations = (IDENTITY, IDENTITY, template)
    result = []
    for mask in MASKS:
        for d in NODES:
            denominator = [d - sum(POLES[permutations[j][h]]
                                    for j in range(3) if mask >> j & 1)
                           for h in range(4)]
            result.append([
                sum((basis[permutations[j][h]] / denominator[h]
                     for h in range(4)), Q(0)) if mask >> j & 1 else Q(0)
                for j in range(3) for basis in BASIS
            ])
    return result


def forbidden_orthants(dual):
    """All strict orthants compatible with a nonzero vector in this plane.

    The affine chart (1,t) is partitioned by all zero-coordinate roots.
    Test those roots, one point per complementary interval, both orientations,
    and the omitted projective point (0,1). Zero coordinates allow both signs.
    """
    a, b = dual
    roots = sorted({-Q(x, y) for x, y in zip(a, b) if y})
    assert roots
    samples = [(Q(0), Q(1))]
    samples += [(Q(1), t) for t in roots]
    samples += [(Q(1), roots[0] - 1), (Q(1), roots[-1] + 1)]
    samples += [(Q(1), (x + y) / 2) for x, y in zip(roots, roots[1:])]
    forbidden = set()
    for u, v in samples:
        z = [x * u + y * v for x, y in zip(a, b)]
        assert any(z)
        zeros = [i for i, value in enumerate(z) if not value]
        for orientation in (-1, 1):
            base = sum(1 << i for i, value in enumerate(z) if orientation * value > 0)
            for bits in product((0, 1), repeat=len(zeros)):
                forbidden.add(base + sum(bit << i for i, bit in zip(zeros, bits)))
    return forbidden


def signs(pattern):
    return [1 if pattern >> i & 1 else -1 for i in range(8)]


def audit_templates():
    matrices = [matrix(template) for template in TEMPLATES]
    forbidden_sets = []
    for a, dual, reps in zip(matrices, DUALS, FORBIDDEN_REPS):
        # The last two coordinates prove the two dual vectors independent.
        assert dual[0][6] and dual[0][7] == 0
        assert dual[1][6] == 0 and dual[1][7]
        assert all(sum(a[i][j] * z[i] for i in range(8)) == 0
                   for z in dual for j in range(6))
        assert any(inverse([a[i] for i in subset]) is not None
                   for subset in combinations(range(8), 6))
        forbidden = forbidden_orthants(dual)
        assert forbidden == set(reps) | {255 - p for p in reps}
        forbidden_sets.append(forbidden)
    assert not set.intersection(*forbidden_sets)
    for d in NODES:
        for residue in BASIS:
            assert sum(residue[h] / (d - POLES[h]) for h in range(4)) == 0
    return matrices, forbidden_sets


def construct_certificates(matrices, forbidden_sets):
    vertices = []
    for a in matrices:
        chart = []
        for subset in combinations(range(8), 6):
            inv = inverse([a[i] for i in subset])
            if inv is not None:
                chart.append((subset, inv))
        vertices.append(chart)
    certificates = []
    for pattern in range(256):
        desired = signs(pattern)
        for chart, (a, forbidden) in enumerate(zip(matrices, forbidden_sets)):
            if pattern in forbidden:
                continue
            for subset, inv in vertices[chart]:
                theta = matvec(inv, [desired[i] for i in subset])
                if all(y * value >= 1 for y, value in zip(desired, matvec(a, theta))):
                    certificates.append({"pattern": pattern, "template": chart,
                                         "theta": [str(v) for v in theta]})
                    break
            else:
                continue
            break
        else:
            raise AssertionError(f"No exact rational witness for pattern {pattern}")
    return certificates


def audit_certificates(certificates):
    assert len(certificates) == 256
    seen = set()
    minimum_margin = None
    for certificate in certificates:
        pattern = certificate["pattern"]
        assert isinstance(pattern, int) and 0 <= pattern < 256 and pattern not in seen
        seen.add(pattern)
        template = certificate["template"]
        assert isinstance(template, int) and 0 <= template < 3
        theta = tuple(map(Q, certificate["theta"]))
        assert len(theta) == 6
        permutations = (IDENTITY, IDENTITY, TEMPLATES[template])
        residues = [[theta[2*j] * BASIS[0][h] + theta[2*j+1] * BASIS[1][h]
                     for h in range(4)] for j in range(3)]
        for u, mask in product((0, 1), range(8)):
            score = Q(0)
            for h in range(4):
                slopes = (1,) + tuple(POLES[permutations[j][h]] for j in range(3))
                assert all(slope > 0 for slope in slopes)
                assert sum(slopes) <= 13
                denominator = 14 - u - sum(slopes[j+1] for j in range(3)
                                            if mask >> j & 1)
                assert denominator >= 1
                # An explicit original FracAtom realization, with delta=0.
                alpha = Q(1, 28)
                rho = tuple(Q(slope) / (1 - alpha) for slope in slopes)
                gamma = 14 - sum(rho)
                assert alpha > 0 and gamma > 0 and all(t > 0 for t in rho)
                numerator_coefficients = (Q(0),) + tuple(
                    residues[j][permutations[j][h]] for j in range(3))
                m = tuple(-c / slope for c, slope in zip(numerator_coefficients, slopes))
                eta = -sum(a * b for a, b in zip(rho, m))
                x = (u,) + tuple((mask >> j) & 1 for j in range(3))
                original_denominator = gamma + sum(rho[i] * (alpha if x[i] else 1)
                                                    for i in range(4))
                numerator = sum(residues[j][permutations[j][h]] for j in range(3)
                                if mask >> j & 1)
                original_numerator = eta + sum(rho[i] * (alpha if x[i] else 1) * m[i]
                                                for i in range(4))
                assert original_denominator == denominator
                assert original_numerator == numerator
                score += numerator / denominator
            if mask.bit_count() <= 1:
                assert score == 0
            else:
                output_index = 2 * MASKS.index(mask) + u
                margin = signs(pattern)[output_index] * score
                assert margin >= 1
                minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
    assert seen == set(range(256))
    return minimum_margin


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-certificates", action="store_true")
    args = parser.parse_args()
    matrices, forbidden_sets = audit_templates()
    if args.write_certificates:
        certificates = construct_certificates(matrices, forbidden_sets)
        audit_certificates(certificates)
        CERT_PATH.write_text(json.dumps(certificates, indent=2) + "\n")
    certificates = json.loads(CERT_PATH.read_text())
    minimum_margin = audit_certificates(certificates)
    print("PASS: 3 rank-six rational charts; forbidden counts 32, 20, 20; empty intersection")
    print("PASS: all 256 sign patterns have exact rational four-head witnesses")
    print(f"PASS: all cube denominators >= 1; all original FracAtom parameters positive; sign margin >= {minimum_margin}")
    print("PASS: all eight axis vertices have exactly zero score for every certificate")


if __name__ == "__main__":
    main()
