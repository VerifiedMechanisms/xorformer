#!/usr/bin/env python3
"""Normalize each ordinary fraction after removing its affine anchor values.

For t=x or 1-x, b_i>0, P=sum b_i and B=1+b.t, use
g_i=(1+P)*t_i*sum_{j!=i}(b_j*t_j)/((P-b_i)*B).
On the Boolean cube these features lie in [0,1]. A shared affine score
plus M such units uses M+1 admissible heads. This is a finite heuristic,
not a universal construction. Run substantial computations through heavy.
"""
import argparse
from fractions import Fraction
import json
import math
import os
from pathlib import Path
import sys
import time
from tempfile import TemporaryDirectory

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
import mpmath as mp
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
from search_confluent_varpro import rational_head, EndSearch
from search_shared_affine_varpro import score_gradient as shared_score
from search_sign_scores import exact_check
from search_varpro_scores import convex_hinge_fit


def excluded_sums(values):
    """Sum all but one entry without subtracting nearly equal numbers."""
    zero = np.zeros_like(values[..., :1])
    before = np.concatenate((zero, np.cumsum(values[..., :-1], axis=-1)), axis=-1)
    after = np.concatenate((np.cumsum(values[..., :0:-1], axis=-1)[..., ::-1], zero), axis=-1)
    return before+after


def geometry(t, logs):
    b = np.exp(logs)
    p = b.sum(axis=1)
    pm = excluded_sums(b)
    v = excluded_sums(t*b[None])
    denominator = 1+np.einsum("xhi,hi->xh", t, b)
    g = t*(v/pm[None])*((1+p)[None, :, None]/denominator[:, :, None])
    return b, p, pm, denominator, g


def features(x, t, logs):
    return np.column_stack((np.ones(len(x)), x, geometry(t, logs)[-1].reshape(len(x), -1)))


def score_gradient(x, t, labels, logs, coefficient):
    b, p, pm, denominator, g = geometry(t, logs)
    units, n = logs.shape
    d = coefficient[n+1:].reshape(units, n)
    local = np.einsum("xhi,hi->xh", g, d)
    score = coefficient[0]+x@coefficient[1:n+1]+local.sum(axis=1)
    residual = np.maximum(1-labels*score, 0.)
    weight = -labels*residual/len(x)
    first = (local/(1+p)[None])[:, :, None]
    second = (local/denominator)[:, :, None]*t
    third = ((1+p)[None]/denominator)[:, :, None]*t*excluded_sums(t*(d/pm)[None])
    fourth = excluded_sums(g*(d/pm)[None])
    derivative = b[None]*(first-second+third-fourth)
    gradient = np.einsum("x,xhi->hi", weight, derivative)
    return float(residual@residual/(2*len(x))), score, gradient.ravel()


def from_shared(checkpoint):
    """Import by high-precision algebra; no refit or relabeling is involved."""
    saved = np.load(checkpoint)
    labels, logs = saved["labels"], saved["logs"]
    if "kind" in saved and str(saved["kind"]) == "anchored-affine":
        return labels, saved["orientation"], logs, saved["coefficients"]
    assert "separation" in saved
    units, n = logs.shape
    separation, coefficient = saved["separation"], saved["coefficients"]
    assert np.all(separation != 0), "Zero separation needs a separately bounded perturbation."
    orientation = np.where(separation > 0, 1, -1)
    old_a = coefficient[n+1:].reshape(units, n)
    with mp.workdps(120):
        affine = [mp.mpf(float(z)) for z in coefficient[:n+1]]
        result_logs, result_d = [], []
        for h in range(units):
            p = [mp.exp(mp.mpf(float(z-logs[h].max()))) for z in logs[h]]
            total = sum(p)
            q = mp.exp(2*mp.mpf(float(separation[h])))
            a = [mp.mpf(float(z)) for z in old_a[h]]
            for i in range(n):
                affine[i+1] += 2*q*a[i]/(q*q-1)
            if orientation[h] > 0:
                b = [(q-1)*z/total for z in p]
                ordinary = [-q*z/(q-1) for z in a]
            else:
                b = [(1-q)*z/(q*total) for z in p]
                constant = sum(a)/(1-q)
                affine[0] += constant
                ordinary = [-z/(1-q)-constant*bb for z, bb in zip(a, b)]
            summed = sum(b)
            d = []
            for i in range(n):
                pm = sum(b[j] for j in range(n) if j != i)
                d.append(-ordinary[i]*pm/((1+b[i])*(1+summed)))
                linear = ordinary[i]/(1+b[i])
                if orientation[h] > 0:
                    affine[i+1] += linear
                else:
                    affine[0] += linear
                    affine[i+1] -= linear
            result_logs.append([float(mp.log(z)) for z in b])
            result_d.append(list(map(float, d)))
        result_coefficient = np.r_[list(map(float, affine)), np.ravel(result_d)]
    return labels, orientation, np.array(result_logs), result_coefficient


def exact_lift(labels, orientation, logs, coefficient):
    units, n = logs.shape
    d = coefficient[n+1:].reshape(units, n)
    affine = [Fraction(float(z)) for z in coefficient[:n+1]]
    heads = []
    for h in range(units):
        with mp.workdps(150):
            b = [Fraction(str(mp.exp(mp.mpf(float(z))))) for z in logs[h]]
        p = sum(b)
        numerator = [Fraction(0)]
        for i in range(n):
            pm = sum(b[j] for j in range(n) if j != i)
            k = Fraction(float(d[h, i]))*(1+p)/pm
            numerator.append(-k*(1+b[i]))
            if orientation[h] > 0:
                affine[i+1] += k
            else:
                affine[0] += k
                affine[i+1] -= k
        heads.append(rational_head(numerator, [Fraction(1)]+b, orientation[h]))
    heads.append(rational_head(affine, [Fraction(1)]+[Fraction(0)]*n, 1))
    cert = {"n": n, "labels": labels.astype(int).tolist(), "heads": heads,
            "bias": [0, 1], "scope": "This finite truth table only; no universal bound.",
            "anchored_affine_lift": {"units": units, "affine_correction_heads": 1}}
    check = exact_check(cert, precision=224)
    if not check["certified"]:
        return None, check
    cert["verification"] = check
    return cert, check


class Problem:
    def __init__(self, labels, orientation, logs, coefficient, out, seconds):
        self.labels, self.orientation = labels, orientation
        self.units, self.n = logs.shape
        self.x = ((np.arange(len(labels))[:, None] >> np.arange(self.n)) & 1).astype(float)
        self.t = np.where(orientation[None, :, None] > 0, self.x[:, None], 1-self.x[:, None])
        assert self.n >= 2 and np.all(np.abs(logs) <= 35)
        self.initial, self.previous = logs.ravel(), coefficient
        self.out, self.start = out, time.monotonic()
        self.deadline = self.start+seconds
        self.events, self.best, self.certificate = [], None, None

    def objective(self, parameters):
        if time.monotonic() >= self.deadline or (self.out/"STOP").exists():
            raise EndSearch
        logs = parameters.reshape(self.units, self.n)
        feature = features(self.x, self.t, logs)
        q, r = la.qr(feature, mode="economic", check_finite=False)
        initial = q.T@(feature@self.previous)
        fit = convex_hinge_fit(self.labels[:, None]*q, initial, "newton", 0.)
        coefficient = la.solve_triangular(r, fit.x, check_finite=False)
        self.previous = coefficient
        loss, score, gradient = score_gradient(self.x, self.t, self.labels, logs, coefficient)
        event = {"evaluation": len(self.events), "seconds": time.monotonic()-self.start,
                 "loss": loss, "errors": int((self.labels*score <= 0).sum()),
                 "minimum_margin": float((self.labels*score).min()),
                 "inner_gradient": float(np.max(np.abs(fit.jac))),
                 "direct_qr_score_discrepancy": float(np.max(np.abs(score-q@fit.x))),
                 "outer_gradient_norm": float(la.norm(gradient)),
                 "maximum_absolute_coefficient": float(np.abs(coefficient).max())}
        self.events.append(event)
        print(json.dumps(event), flush=True)
        if self.best is None or loss < self.best[0]:
            self.best = (loss, parameters.copy(), coefficient.copy())
            np.savez(self.out/"checkpoint.npz", labels=self.labels, orientation=self.orientation,
                     logs=logs, coefficients=coefficient, kind="anchored-affine")
        if event["minimum_margin"] > 1e-5:
            cert, check = exact_lift(self.labels, self.orientation, logs, coefficient)
            event["exact_check"] = check
            if cert is not None:
                (self.out/"certificate.json").write_text(json.dumps(cert)+"\n")
                self.certificate = "certificate.json"
                raise EndSearch
        return loss, gradient

    def run(self):
        try:
            result = opt.minimize(self.objective, self.initial, jac=True, method="L-BFGS-B",
                                  bounds=[(-35, 35)]*len(self.initial),
                                  options={"maxiter": 100000, "maxfun": 100000,
                                           "ftol": 1e-15, "gtol": 1e-10,
                                           "maxls": 35, "maxcor": 50})
            termination = str(result.message)
        except EndSearch:
            termination = "certificate" if self.certificate else "budget or stop file"
        result = {"n": self.n, "units": self.units, "lifted_heads": self.units+1,
                  "seconds": time.monotonic()-self.start, "termination": termination,
                  "best_loss": None if self.best is None else self.best[0],
                  "certificate": self.certificate, "events": self.events,
                  "scope": "Finite anchored-affine search; no universal theorem.",
                  "failure_is_not_a_lower_bound": True}
        (self.out/"result.json").write_text(json.dumps(result)+"\n")
        print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


def self_test():
    rng = np.random.default_rng(2026112214)
    n, units = 4, 2
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    orientation = np.array([-1, 1])
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    logs = rng.normal(size=(units, n))
    coefficient = rng.normal(0, .2, n+1+units*n)
    labels = rng.choice([-1., 1.], len(x))
    loss, score, gradient = score_gradient(x, t, labels, logs, coefficient)
    numerical = []
    for i in range(logs.size):
        step = np.zeros(logs.size)
        step[i] = 1e-5
        numerical.append((score_gradient(x, t, labels, logs+step.reshape(logs.shape), coefficient)[0]-
                          score_gradient(x, t, labels, logs-step.reshape(logs.shape), coefficient)[0])/2e-5)
    error = float(np.max(np.abs(gradient-numerical)))
    assert error < 1e-8, error
    g = geometry(t, logs)[-1]
    assert np.min(g) >= 0 and np.max(g) <= 1+1e-14
    extreme = np.array([[35., -35., -34., -33.], [-35., 35., -34., -33.]])
    eg = geometry(t, extreme)[-1]
    assert np.isfinite(eg).all() and np.min(eg) >= 0 and np.max(eg) <= 1+1e-14
    strict = np.where(score > 0, 1., -1.)
    cert, check = exact_lift(strict, orientation, logs, coefficient)
    assert cert is not None, check
    parity = 1-2*(x.sum(axis=1) % 2)
    def reduced(ll):
        feature = features(x, t[:, :1], ll)
        q, r = la.qr(feature, mode="economic")
        fit = convex_hinge_fit(parity[:, None]*q, q.T@parity, "newton", 0.)
        cc = la.solve_triangular(r, fit.x)
        assert np.max(np.abs(fit.jac)) < 1e-8
        return score_gradient(x, t[:, :1], parity, ll, cc)
    loss, _, gradient = reduced(logs[:1])
    numerical = []
    for i in range(n):
        step = np.zeros((1, n))
        step[0, i] = 1e-5
        numerical.append((reduced(logs[:1]+step)[0]-reduced(logs[:1]-step)[0])/2e-5)
    reduced_error = float(np.max(np.abs(gradient-numerical)))
    assert loss > 0 and reduced_error < 1e-7, (loss, reduced_error)
    import_records = []
    for separation in (np.array([-.8, .6]), np.array([-1e-5, 2e-5]), np.array([-12., 10.])):
        old_coefficient = rng.normal(0, .2, n+1+units*n)
        old_score = shared_score(x, labels, logs, separation, old_coefficient)[1]
        with TemporaryDirectory() as directory:
            path = Path(directory)/"shared.npz"
            np.savez(path, labels=labels, logs=logs, separation=separation,
                     coefficients=old_coefficient, kind="shared-affine")
            _, imported_orientation, imported_logs, imported_coefficient = from_shared(path)
        imported_t = np.where(imported_orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
        new_score = score_gradient(x, imported_t, labels, imported_logs, imported_coefficient)[1]
        discrepancy = float(np.max(np.abs(new_score-old_score)))
        assert discrepancy < 1e-10, (separation, discrepancy)
        import_records.append({"separation": separation.tolist(), "score_discrepancy": discrepancy})
    return {"fixed_coefficient_gradient_error": error, "refitted_gradient_error": reduced_error,
            "positive_refitted_loss": loss, "extreme_feature_minimum": float(eg.min()),
            "extreme_feature_maximum": float(eg.max()), "exact_check": check,
            "shared_import_checks": import_records,
            "scope": "Implementation diagnostics only."}, cert


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", nargs="?", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.self_test:
        result, cert = self_test()
        (args.out/"diagnostic.json").write_text(json.dumps(result, indent=2)+"\n")
        (args.out/"certificate.json").write_text(json.dumps(cert)+"\n")
        print(json.dumps(result), flush=True)
    else:
        assert args.checkpoint is not None
        Problem(*from_shared(args.checkpoint), args.out, args.seconds).run()
