#!/usr/bin/env python3
"""Audit fixed-denominator feasibility with an Arb orthogonal basis.

Uses python-flint, installed separately in the run's output directory.
The inner LP is floating point; success is accepted only after an independent
exact Fraction check of exported integer coefficients. Use heavy.
"""
import argparse
from fractions import Fraction
import json
from math import lcm
import os
from pathlib import Path
import time
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
import scipy.sparse as sp
from flint import arb, arb_mat, ctx, fmpq
from verify_certificate import verify


def rational_ball(value):
    a, b = float(value).as_integer_ratio()
    return arb(fmpq(a, b))


def exact_midpoint(value):
    mantissa, exponent = value.mid().man_exp()
    exponent = int(exponent)
    return Fraction(int(mantissa))*Fraction(2)**exponent


def select_hinge_basis(q, margins, multipliers):
    """Choose candidate equality rows; the caller must refit and audit them.

    Fractional dual variables must be included. Complete them using near-unit
    margins with large residual row norm. This selection is numerical and is
    never itself accepted as a proof of primal or dual feasibility.
    """
    dimension = q.shape[1]
    selected = np.flatnonzero((multipliers > 1e-7) & (multipliers < 1-1e-7)).tolist()
    if len(selected) > dimension:
        raise ArithmeticError("too many fractional dual variables")
    if selected:
        basis, rr = la.qr(q[selected].T, mode="economic", check_finite=False)
        if np.min(np.abs(np.diag(rr))) < 1e-12:
            raise ArithmeticError("fractional equality rows are numerically dependent")
    else:
        basis = np.empty((dimension,0))
    candidates = [int(i) for i in np.flatnonzero(np.abs(margins-1) < 1e-5)
                  if i not in set(selected)]
    while len(selected) < dimension:
        if not candidates:
            raise ArithmeticError("not enough candidate hinge equalities")
        residual = q[candidates]-(q[candidates]@basis)@basis.T
        norms = la.norm(residual,axis=1)
        index = int(np.argmax(norms))
        if norms[index] < 1e-12:
            raise ArithmeticError("candidate hinge equalities have insufficient numerical rank")
        selected.append(candidates.pop(index))
        basis = np.column_stack((basis,residual[index]/norms[index]))
    return np.array(selected,dtype=int)


def build_basis(logs, orientation, bits=512, progress=False):
    started = time.monotonic()
    ctx.prec = bits
    h = len(orientation)
    n = np.asarray(logs).size//h
    b_float = np.exp(np.asarray(logs).reshape(h, n))
    b = [[rational_ball(v) for v in row] for row in b_float]
    dimension = 1+n*h
    rows = []
    denominators = []
    for x in range(1 << n):
        row = [arb(1)]
        denominator_row = []
        for j in range(h):
            active = [bool(x >> i & 1) == (orientation[j] > 0) for i in range(n)]
            denominator = arb(1)+sum((b[j][i] for i in range(n) if active[i]), arb(0))
            denominator_row.append(denominator)
            row.extend(arb(int(flag))/denominator for flag in active)
        rows.append(row)
        denominators.append(denominator_row)
    features = arb_mat(rows)
    del rows
    if progress:
        print(json.dumps({"stage": "features", "seconds": time.monotonic()-started,
                          "n": n, "heads": h, "bits": bits}), flush=True)
    gram = features.transpose()*features
    lower = [[arb(0) for _ in range(dimension)] for _ in range(dimension)]
    for i in range(dimension):
        for j in range(i+1):
            value = gram[i,j]-sum((lower[i][k]*lower[j][k] for k in range(j)), arb(0))
            if i == j:
                if not value > 0:
                    raise ArithmeticError(f"Cholesky pivot {i} is not certified positive at {bits} bits")
                lower[i][j] = value.sqrt()
            else:
                lower[i][j] = value/lower[j][j]
        if progress and i % 25 == 0:
            print(json.dumps({"stage": "cholesky", "row": i,
                              "seconds": time.monotonic()-started}), flush=True)
    inverse = arb_mat(lower).transpose().inv()
    orthogonal = features*inverse
    q = np.array([[float(orthogonal[i,j].mid()) for j in range(dimension)]
                  for i in range(1 << n)])
    return features, inverse, q, b, b_float, denominators


def run(checkpoint, out, bits):
    started = time.monotonic()
    saved = np.load(checkpoint)
    labels = saved["labels"].astype(int)
    orientation = saved["orientation"].astype(int)
    n, h = len(labels).bit_length()-1, len(orientation)
    assert len(labels) == 1 << n
    features, inverse, q, b, b_float, denominators = build_basis(
        saved["logs"], orientation, bits, progress=True)
    dimension = 1+n*h
    # QR here only improves the double-precision conditioning of the LP.
    # Retain the transformation to recover coefficients in the Arb basis.
    qq, rr = la.qr(q, mode="economic", check_finite=False)
    matrix = sp.hstack((-sp.csr_matrix(labels[:,None]*qq), -sp.eye(len(labels))), format="csr")
    fit = opt.linprog(np.r_[np.zeros(dimension), np.ones(len(labels))],
                     A_ub=matrix, b_ub=-np.ones(len(labels)),
                     bounds=[(None,None)]*dimension+[(0,None)]*len(labels),
                     method="highs")
    if not fit.success:
        raise RuntimeError(fit.message)
    coordinates = la.solve_triangular(rr, fit.x[:dimension], check_finite=False)
    coeff_ball = inverse*arb_mat([[rational_ball(v)] for v in coordinates])
    coefficients = [exact_midpoint(coeff_ball[i,0]) for i in range(dimension)]
    margins = labels*(qq @ fit.x[:dimension])
    record = {"n": n, "heads": h, "bits": bits,
              "seconds": time.monotonic()-started,
              "lp_loss": float(fit.fun), "floating_errors": int((margins <= 0).sum()),
              "floating_minimum_margin": float(margins.min()),
              "certificate": None,
              "scope": "Fixed denominator list on one finite truth table only."}
    if margins.min() > 1e-6:
        heads = []
        for j in range(h):
            aa = [Fraction(0)]+coefficients[1+j*n:1+(j+1)*n]
            bb = [Fraction(1)]+[Fraction(float(v)) for v in b_float[j]]
            if orientation[j] < 0:
                aa = [sum(aa)]+[-v for v in aa[1:]]
                bb = [sum(bb)]+[-v for v in bb[1:]]
            scale = lcm(*(v.denominator for v in aa+bb))
            heads.append({"numerator": [int(v*scale) for v in aa],
                          "denominator": [int(v*scale) for v in bb]})
        candidate = out/"candidate.json"
        bias = coefficients[0]
        candidate.write_text(json.dumps({"n": n, "heads": heads,
            "labels": labels.tolist(), "bias": [bias.numerator, bias.denominator],
            "scope": record["scope"]})+"\n")
        check = verify(candidate)
        candidate.rename(out/"certificate.json")
        record["certificate"] = "certificate.json"
        record["verification"] = check
    (out/"result.json").write_text(json.dumps(record)+"\n")
    print(json.dumps(record), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--bits", type=int, default=512)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.bits)
