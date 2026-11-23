#!/usr/bin/env python3
"""Exact small tests for tangent branches of a full-cube reciprocal identity.

The seven-point result is finite, not an asymptotic compiler.  Every one of
its 128 labels is checked using six strictly admissible affine ratios on
the original five-dimensional cube.  Optional eight-point enumeration is
an exact finite diagnostic, not evidence of a general obstruction.
"""
import argparse
from fractions import Fraction as F
import importlib.util
from itertools import product
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "exact_planes", HERE / "reverse-joint-affine-plane-search.py")
PLANES = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PLANES)
PERMS = ((0, 2, 1), (1, 0, 2))
CUBE = tuple(product((0, 1), repeat=5))
SEVEN = ((1, 0, 1, 1, 0), (1, 0, 1, 1, 1), (1, 0, 0, 1, 0),
         (0, 1, 1, 0, 0), (1, 1, 0, 0, 0), (1, 1, 0, 1, 1),
         (0, 1, 0, 1, 1))
EIGHT = ((1, 0, 1, 1, 0), (1, 0, 1, 1, 1), (0, 0, 1, 1, 1),
         (0, 1, 1, 0, 0), (0, 1, 1, 1, 0), (1, 1, 0, 1, 1),
         (0, 1, 0, 1, 1), (0, 1, 0, 1, 0))


def denominator(x, p, h):
    a, b = x[0]-x[1], x[1]-x[2]
    return 1+4*sum(x[:3])+8*x[3]+16*x[4]+h*a+p[h]*b


def row(x, p):
    b = x[1]-x[2]
    values = [-F(1, denominator(x, p, h)**2) for h in range(3)]
    return values+[b*v for v in values]


def determinant(matrix):
    rows = [list(r) for r in matrix]
    value = F(1)
    for j in range(len(rows)):
        pivot = next((i for i in range(j, len(rows)) if rows[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            rows[j], rows[pivot] = rows[pivot], rows[j]
            value = -value
        value *= rows[j][j]
        for i in range(j+1, len(rows)):
            scale = rows[i][j]/rows[j][j]
            rows[i] = [a-scale*b for a, b in zip(rows[i], rows[j])]
    return value


def normal_signs(matrix):
    normal = [(-1)**i*determinant(matrix[:i]+matrix[i+1:])
              for i in range(len(matrix))]
    assert all(normal)
    assert all(sum(normal[i]*matrix[i][j] for i in range(7)) == 0
               for j in range(6))
    return tuple(1 if x > 0 else -1 for x in normal)


def certify_perturbation(p, direction, pattern, points):
    tangents = [sum(a*b for a, b in zip(row(x, p), direction)) for x in points]
    assert all(tangents)
    margin = min(map(abs, tangents))
    bound = max(abs(direction[h])+abs(direction[h+3]) for h in range(3))
    eps = min(F(1, 4)/(1+bound), margin/(24*(1+bound)**2))
    # These are all coefficients of the three perturbed affine denominators.
    for h in range(3):
        d, q = direction[h], direction[h+3]
        assert 1+eps*d > 0
        assert min(4+h, 4+p[h]-h+eps*q, 4-p[h]-eps*q, 8, 16) > 0
    for x in CUBE:
        for h in range(3):
            delta = direction[h]+direction[h+3]*(x[1]-x[2])
            assert denominator(x, p, h)+eps*delta > 0
    actual = []
    for x in points:
        perturbed = sum(1/(F(denominator(x, p, h))+eps*(
            direction[h]+direction[h+3]*(x[1]-x[2]))) for h in range(3))
        baseline = sum(F(1, denominator(x, PERMS[0], h)) for h in range(3))
        actual.append(perturbed-baseline)
    assert all(actual)
    assert sum((v > 0) << i for i, v in enumerate(actual)) == pattern


def main(check_eight):
    for x in CUBE:
        assert sorted(denominator(x, PERMS[0], h) for h in range(3)) == sorted(
            denominator(x, PERMS[1], h) for h in range(3))
        assert min(denominator(x, p, h) for p in PERMS for h in range(3)) > 0
    ranks = [len(PLANES.independent_columns([row(x, p) for x in CUBE])) for p in PERMS]
    union_rank = len(PLANES.independent_columns(
        [row(x, PERMS[0])+row(x, PERMS[1]) for x in CUBE]))
    normals = [normal_signs([row(x, p) for x in SEVEN]) for p in PERMS]
    assert normals[0] != normals[1] and normals[0] != tuple(-x for x in normals[1])
    witnesses = {}
    counts = []
    for p in PERMS:
        found, complete = PLANES.orthants([row(x, p) for x in SEVEN], [F(0)]*7)
        assert complete
        counts.append(len(found))
        for pattern, direction in found.items():
            witnesses[pattern] = (p, direction)
    assert len(witnesses) == 128
    for pattern, (p, direction) in witnesses.items():
        certify_perturbation(p, direction, pattern, SEVEN)
    result = dict(cube_identity_points=32, restricted_ranks=ranks,
                  union_rank=union_rank, normal_signs=normals,
                  seven_point_branch_counts=counts,
                  six_head_strict_certificates=len(witnesses),
                  seven_points=SEVEN)
    if check_eight:
        covered = set()
        counts = []
        for p in PERMS:
            found, complete = PLANES.orthants([row(x, p) for x in EIGHT], [F(0)]*8)
            assert complete
            counts.append(len(found))
            covered.update(found)
        assert counts == [240, 240] and len(covered) == 244
        result.update(eight_point_branch_counts=counts,
                      eight_point_union_count=len(covered), eight_points=EIGHT)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-eight", action="store_true")
    main(parser.parse_args().check_eight)
