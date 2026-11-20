#!/usr/bin/env python3
"""Hinge variable projection with high-precision primal and dual refits.

The LP chooses a basis numerically. Arb then refits both its primal equality
constraints and dual annihilation constraints. This is a numerical search,
not a theorem about feasibility or convergence. Use heavy.
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
from flint import arb, arb_mat
from refit_high_precision import build_basis, exact_midpoint, rational_ball
from search_varpro_scores import Problem, TimeLimit, Certified
from verify_certificate import verify


def fit_hinge(logs, orientation, labels, bits, lp_seconds=120):
    features, inverse, q, b, b_float, den = build_basis(logs, orientation, bits)
    rows, columns = q.shape
    h = len(orientation)
    n = (columns-1)//h
    qq, rr = la.qr(q, mode="economic", check_finite=False)
    matrix = sp.hstack((-sp.csr_matrix(labels[:,None]*qq), -sp.eye(rows)), format="csr")
    fit = opt.linprog(np.r_[np.zeros(columns), np.ones(rows)],
                     A_ub=matrix, b_ub=-np.ones(rows),
                     bounds=[(None,None)]*columns+[(0,None)]*rows,
                     method="highs",
                     options={"dual_feasibility_tolerance": 1e-9,
                              "primal_feasibility_tolerance": 1e-9,
                              "time_limit": lp_seconds})
    if not fit.success:
        raise ArithmeticError(f"Inner LP did not produce an optimum: {fit.message}")
    margin = labels*(qq @ fit.x[:columns])
    if margin.min() > 1e-6:
        coordinates = la.solve_triangular(rr, fit.x[:columns], check_finite=False)
        coefficients = inverse*arb_mat([[rational_ball(v)] for v in coordinates])
        scores = features*coefficients
        actual_margin = np.array([int(labels[i])*float(scores[i,0].mid()) for i in range(rows)])
        return (float(np.maximum(1-actual_margin, 0).mean()), np.zeros(n*h),
                coefficients, actual_margin, b_float)
    kinks = np.flatnonzero(np.abs(margin-1) < 1e-6)
    if len(kinks) != columns:
        # No claim that a degenerate LP vertex has this many independent
        # active margin equations. Such a state is rejected explicitly.
        raise ArithmeticError(f"Expected {columns} independent kinks, found {len(kinks)}")
    kink_set = set(kinks.tolist())
    active = [i for i in range(rows) if i not in kink_set and margin[i] < 1]
    fk = arb_mat([[features[i,j] for j in range(columns)] for i in kinks])
    coefficients = fk.solve(arb_mat([[int(labels[i])] for i in kinks]))
    # w is the derivative of the hinge objective with respect to scores.
    # On strictly active hinges w_i=-y_i, and on inactive hinges it is zero.
    dual_rhs = arb_mat([[sum((features[i,j]*int(labels[i]) for i in active), arb(0))]
                       for j in range(columns)])
    wk = fk.transpose().solve(dual_rhs)
    w = [arb(0) for _ in range(rows)]
    for i in active:
        w[i] = arb(-int(labels[i]))
    for j, i in enumerate(kinks):
        w[i] = wk[j,0]
        multiplier = float((-int(labels[i])*w[i]).mid())
        if not -1e-7 <= multiplier <= 1+1e-7:
            raise ArithmeticError(f"Refitted dual multiplier outside [0,1]: {multiplier}")
    scores = features*coefficients
    actual_margin = np.array([int(labels[i])*float(scores[i,0].mid()) for i in range(rows)])
    if (np.abs(actual_margin[kinks]-1).max() > 1e-7 or
        any(actual_margin[i] > 1+1e-7 for i in active) or
        any(actual_margin[i] < 1-1e-7 for i in range(rows)
            if i not in kink_set and i not in active)):
        raise ArithmeticError("Numerically chosen LP basis fails primal consistency after refitting")
    gradient = [[arb(0) for _ in range(n)] for _ in range(h)]
    for x in range(rows):
        if w[x].is_zero():
            continue
        for j in range(h):
            indices = [i for i in range(n) if bool(x >> i & 1) == (orientation[j] > 0)]
            numerator = sum((coefficients[1+j*n+i,0] for i in indices), arb(0))
            factor = -w[x]*numerator/(den[x][j]*den[x][j])
            for i in indices:
                gradient[j][i] += factor*b[j][i]
    grad = np.array([[float(v.mid())/rows for v in row] for row in gradient])
    loss = float(np.maximum(1-actual_margin, 0).mean())
    return loss, grad.ravel(), coefficients, actual_margin, b_float


def export_precise(n, orientation, labels, coeff_ball, b_float):
    coefficients = [exact_midpoint(coeff_ball[i,0]) for i in range(coeff_ball.nrows())]
    heads = []
    for j in range(len(orientation)):
        aa = [Fraction(0)]+coefficients[1+j*n:1+(j+1)*n]
        bb = [Fraction(1)]+[Fraction(float(v)) for v in b_float[j]]
        if orientation[j] < 0:
            aa = [sum(aa)]+[-v for v in aa[1:]]
            bb = [sum(bb)]+[-v for v in bb[1:]]
        scale = lcm(*(v.denominator for v in aa+bb))
        heads.append({"numerator": [int(v*scale) for v in aa],
                      "denominator": [int(v*scale) for v in bb]})
    bias = coefficients[0]
    return {"n": n, "heads": heads, "labels": labels.astype(int).tolist(),
            "bias": [bias.numerator, bias.denominator],
            "scope": "This finite truth table only; not a universal upper bound."}


class ArbProblem(Problem):
    def objective(self, logs):
        if time.monotonic() >= self.deadline:
            raise TimeLimit
        loss, gradient, cc, margin, b_float = fit_hinge(logs, self.orientation,
                                                       self.y, self.bits,
                                                       getattr(self, "lp_seconds", 120))
        coefficients = np.array([float(cc[i,0].mid()) for i in range(cc.nrows())])
        self.evaluations += 1
        errors = int((margin <= 0).sum())
        self.best_errors = min(self.best_errors, errors)
        if loss < self.best_loss:
            self.best_loss = loss
            self.best_logs, self.best_coeff = logs.copy(), coefficients.copy()
            np.savez(self.out/"checkpoint.npz", logs=logs, coefficients=coefficients,
                     orientation=self.orientation, labels=self.y)
        event = {"evaluation": self.evaluations, "seconds": time.monotonic()-self.start,
                 "loss": loss, "errors": errors, "minimum_margin": float(margin.min()),
                 "gradient_norm": float(la.norm(gradient)), "bits": self.bits}
        self.events.append(event)
        print(json.dumps(event), flush=True)
        if self.check_certificate and margin.min() > 1e-6:
            candidate = self.out/"candidate.json"
            candidate.write_text(json.dumps(export_precise(self.n, self.orientation,
                                           self.y, cc, b_float))+"\n")
            check = verify(candidate)
            candidate.rename(self.out/"certificate.json")
            (self.out/"independent-check.json").write_text(json.dumps(check)+"\n")
            self.certificate = "certificate.json"
            self.certified_logs, self.certified_coeff = logs.copy(), coefficients.copy()
            raise Certified
        return loss, gradient


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--bits", type=int, default=512)
    parser.add_argument("--seconds", type=float, default=28800)
    parser.add_argument("--gradient-check", action="store_true")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    saved = np.load(args.checkpoint)
    labels, orientation, logs = saved["labels"], saved["orientation"], saved["logs"]
    n, h = len(labels).bit_length()-1, len(orientation)
    if args.gradient_check:
        np.savez(args.out/"input.npz", logs=logs, orientation=orientation, labels=labels)
        loss, grad, *_ = fit_hinge(logs, orientation, labels, args.bits)
        direction = np.random.default_rng(200000).normal(size=logs.shape)
        direction /= la.norm(direction)
        results = []
        for eps in (1e-4, 1e-5, 1e-6):
            plus = fit_hinge(logs+eps*direction, orientation, labels, args.bits)[0]
            minus = fit_hinge(logs-eps*direction, orientation, labels, args.bits)[0]
            results.append({"epsilon": eps, "finite_difference": (plus-minus)/(2*eps)})
        record = {"loss": loss, "analytic": float(grad @ direction.ravel()),
                  "directions": results, "bits": args.bits}
        (args.out/"gradient-check.json").write_text(json.dumps(record)+"\n")
        print(json.dumps(record), flush=True)
        return
    problem = ArbProblem(n, h, 200000, args.seconds, args.out, "arb", score_penalty=0)
    problem.bits, problem.y, problem.orientation = args.bits, labels.copy(), orientation.copy()
    problem.initial_logs = logs.copy()
    problem.t = np.where(orientation[None,:,None] > 0,
                         problem.x[:,None,:], 1-problem.x[:,None,:])
    basis_failures = []
    while True:
        try:
            result = problem.run()
            break
        except ArithmeticError as error:
            basis_failures.append(str(error))
            print(json.dumps({"basis_rejected": str(error),
                              "count": len(basis_failures)}), flush=True)
            if time.monotonic() >= problem.deadline or len(basis_failures) >= 30:
                result = {"certificate": problem.certificate,
                          "best_loss": problem.best_loss,
                          "failure_is_not_a_lower_bound": True}
                break
            center = problem.best_logs if np.isfinite(problem.best_loss) else logs
            scale = 10.**(-3+len(basis_failures)%3)
            problem.initial_logs = np.clip(center+problem.rng.normal(0, scale, center.shape), -20, 20)
    result["basis_failures"] = basis_failures
    (args.out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "events"}), flush=True)


if __name__ == "__main__":
    main()
