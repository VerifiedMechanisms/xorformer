#!/usr/bin/env python3
"""Independent interval-Newton audit of an affine-ratio loss minimum.

All input decimals specify exact rationals. The contraction mapping theorem
and an interval LDL decomposition certify a strict local minimum inside the
specified box. This imports no optimization code. Requires python-flint.
No conclusion about universal head complexity follows from this audit.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time

from flint import arb, arb_mat, ctx, fmpq


def number(value):
    q = Fraction(value)
    return arb(fmpq(q.numerator, q.denominator))


def derivatives(data, parameters):
    n, heads = data["n"], data["heads"]
    count = 1 << n
    size = 1 + 2*n*heads
    gradient = [arb(0) for _ in range(size)]
    hessian = [[arb(0) for _ in range(size)] for _ in range(size)]
    total_loss = arb(0)
    active = negative = positive = undetermined = 0
    single_head_moment = arb(0)
    for vertex, label in enumerate(data["labels"]):
        score = parameters[0]
        jacobian = [arb(0) for _ in range(size)]
        jacobian[0] = arb(1)
        score_hessian = [[arb(0) for _ in range(size)] for _ in range(size)]
        for head in range(heads):
            bits = [(vertex >> i) & 1 for i in range(n)]
            if data["orientation"][head] < 0:
                bits = [1-v for v in bits]
            ui = [1+head*n+i for i in range(n)]
            bi = [1+heads*n+head*n+i for i in range(n)]
            numerator = sum((parameters[i]*v for i, v in zip(ui, bits)), arb(0))
            denominator = 1 + sum(
                (parameters[i]*v for i, v in zip(bi, bits)), arb(0))
            assert denominator > 0
            inverse = 1/denominator
            score += numerator*inverse
            for i in range(n):
                jacobian[ui[i]] = bits[i]*inverse
                jacobian[bi[i]] = -numerator*bits[i]*inverse**2
                for j in range(n):
                    mixed = -bits[i]*bits[j]*inverse**2
                    score_hessian[ui[i]][bi[j]] = mixed
                    score_hessian[bi[j]][ui[i]] = mixed
                    score_hessian[bi[i]][bi[j]] = (
                        2*numerator*bits[i]*bits[j]*inverse**3)
        margin = label*score
        if margin < 0:
            negative += 1
        elif margin > 0:
            positive += 1
        else:
            undetermined += 1
        residual = 1-margin
        if data["loss_kind"] == "hinge":
            if residual < 0:
                continue
            assert residual > 0, "A hinge kink is not separated"
        active += 1
        weight = label*residual
        total_loss += residual**2/(2*count)
        if heads == 1:
            # M_00 for the full one-head score after bias absorption.
            single_head_moment += weight*inverse**2/count
        for i in range(size):
            gradient[i] -= weight*jacobian[i]/count
            for j in range(size):
                hessian[i][j] += (
                    jacobian[i]*jacobian[j]-weight*score_hessian[i][j])/count
    return (total_loss, gradient, hessian, active, negative, positive,
            undetermined, single_head_moment)


def positive_definite(matrix):
    """Interval LDL with positive pivots proves positive definiteness."""
    size = len(matrix)
    lower = [[arb(0) for _ in range(size)] for _ in range(size)]
    diagonal = []
    for j in range(size):
        pivot = matrix[j][j] - sum(
            (lower[j][k]**2*diagonal[k] for k in range(j)), arb(0))
        assert pivot > 0, ("LDL pivot not positive", j, str(pivot))
        diagonal.append(pivot)
        lower[j][j] = arb(1)
        for i in range(j+1, size):
            lower[i][j] = (matrix[i][j] - sum(
                (lower[i][k]*lower[j][k]*diagonal[k] for k in range(j)),
                arb(0)))/pivot
    return diagonal


def verify(path, out, bits):
    ctx.prec = bits
    started = time.monotonic()
    raw = path.read_bytes()
    data = json.loads(raw)
    n, heads = data["n"], data["heads"]
    assert isinstance(n, int) and n > 0
    assert isinstance(heads, int) and heads > 0
    size = 1+2*n*heads
    assert len(data["labels"]) == 1 << n
    assert all(label in (-1, 1) for label in data["labels"])
    assert len(data["orientation"]) == heads
    assert all(orientation in (-1, 1) for orientation in data["orientation"])
    assert data["loss_kind"] in ("hinge", "square")
    assert len(data["center"]) == size
    center = [number(value) for value in data["center"]]
    radius = number(data["relative_radius"])
    assert radius > 0
    # Integer scales are exact. No floating-point values enter the verifier.
    scales = [arb(1+int(abs(Fraction(value)))) for value in data["center"]]
    box = [c+arb(0, scale*radius) for c, scale in zip(center, scales)]
    assert all(slope > 0 for slope in box[1+n*heads:])
    _, gradient, hessian, point_active, _, _, _, _ = derivatives(data, center)
    (box_loss, _, box_hessian, active, negative, positive,
     undetermined, moment) = derivatives(data, box)
    assert box_loss > 0 and active == point_active
    h0 = [[hessian[i][j]*scales[i]*scales[j] for j in range(size)]
          for i in range(size)]
    hb = [[box_hessian[i][j]*scales[i]*scales[j] for j in range(size)]
          for i in range(size)]
    positive_definite(h0)
    pivots = positive_definite(hb)
    # Let R be the exact inverse of the Hessian at the exact center.
    # Validated inversion encloses R, not an unverified numeric preconditioner.
    inverse = arb_mat(h0).inv()
    offset = -(inverse*arb_mat([[gradient[i]*scales[i]] for i in range(size)]))
    jacobian = arb_mat([[int(i == j) for j in range(size)]
                        for i in range(size)]) - inverse*arb_mat(hb)
    row_bounds, image_bounds = [], []
    for i in range(size):
        row = sum((abs(jacobian[i, j]) for j in range(size)), arb(0))
        image = abs(offset[i, 0])+radius*row
        assert row < 1 and image < radius, (
            "Contraction enclosure failed", i, str(row), str(image))
        row_bounds.append(str(row))
        image_bounds.append(str(image/radius))
    result = {
        "input_sha256": hashlib.sha256(raw).hexdigest(),
        "n": n, "heads": heads, "loss_kind": data["loss_kind"],
        "parameters": size, "vertices_checked": 1 << n,
        "precision_bits": bits,
        "all_slopes_strictly_positive_in_oriented_coordinates": True,
        "active_vertices": active,
        "vertices_with_certified_negative_margin_throughout_box": negative,
        "vertices_with_certified_positive_margin_throughout_box": positive,
        "vertices_with_undetermined_margin_sign": undetermined,
        "loss_interval_throughout_box": str(box_loss),
        "hessian_LDL_pivots": list(map(str, pivots)),
        "contraction_row_bounds": row_bounds,
        "image_to_radius_bounds": image_bounds,
        "unique_stationary_point_in_box": True,
        "strict_local_minimum": True,
        "scope": "One positive local minimum of the specified loss. "
                 "No universal head bound or sign-representation lower bound.",
        "seconds": time.monotonic()-started,
    }
    if heads == 1:
        result["single_head_residual_moment_00"] = str(moment)
        result["single_head_residual_moment_nonzero"] = bool(moment < 0 or moment > 0)
    out.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--bits", type=int, default=384)
    args = parser.parse_args()
    verify(args.input, args.out, args.bits)
