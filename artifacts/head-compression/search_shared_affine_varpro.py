#!/usr/bin/env python3
"""Orientation-crossing rational chart with one shared affine correction.

r=q*(t1-t0)/((q+1)*(q*t1+t0)), q=exp(2*s), t1=sum(p_i*x_i),
t0=sum(p_i*(1-x_i)), p_i>0. Search C(x)+sum A_h(x)*r_h(x).
M units lift to M+1 ordinary heads, including at q=1 by a controlled
perturbation. This finite heuristic makes no universal capacity claim.
Run substantial searches through heavy.
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

# Exact shared corrections can have denominators with tens of thousands of
# digits. These are locally generated certificate integers, not web input.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import mpmath as mp
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
from search_confluent_varpro import dyadic_below, rational_head, EndSearch
from search_sign_scores import exact_check
from search_varpro_scores import convex_hinge_fit


def unpack(parameters, units, n):
    return parameters[:units*n].reshape(units, n), parameters[units*n:]


def geometry(x, logs, separation):
    p = np.exp(logs-logs.max(axis=1, keepdims=True))
    q = np.exp(2*separation)
    t1, t0 = x@p.T, (1-x)@p.T
    b = q*t1+t0
    r = (q/(q+1))*(t1-t0)/b
    return p, q, t1, t0, b, r


def features(x, logs, separation):
    r = geometry(x, logs, separation)[-1]
    return np.column_stack((np.ones(len(x)), x,
                            (r[:, :, None]*x[:, None, :]).reshape(len(x), -1)))


def score_gradient(x, labels, logs, separation, coefficient):
    units, n = logs.shape
    p, q, t1, t0, b, r = geometry(x, logs, separation)
    aa = coefficient[n+1:].reshape(units, n)
    ax = x@aa.T
    score = coefficient[0]+x@coefficient[1:n+1]+(ax*r).sum(axis=1)
    residual = np.maximum(1-labels*score, 0.)
    weight = -labels*residual/len(x)
    z = weight[:, None]*ax*q/(b*b)
    glog = p*(p.sum(axis=1)[:, None]*(x.T@z).T-(z*t1).sum(axis=0)[:, None])
    gs = (weight[:, None]*ax*r*(2/(q+1)-2*q*t1/b)).sum(axis=0)
    return float(residual@residual/(2*len(x))), score, np.r_[glog.ravel(), gs]


def exact_lift(labels, logs, separation, coefficient, precision=224):
    """Round to rational data, certify that data, then compile exact heads."""
    units, n = logs.shape
    cf = list(map(lambda z: Fraction(float(z)), coefficient[:n+1]))
    aa = coefficient[n+1:].reshape(units, n)
    data = []
    for h in range(units):
        with mp.workdps(150):
            shifted = logs[h]-logs[h].max()
            p = [Fraction(str(mp.exp(mp.mpf(float(z))))) for z in shifted]
            q = Fraction(str(mp.exp(2*mp.mpf(float(separation[h])))))
        a = list(map(lambda z: Fraction(float(z)), aa[h]))
        data.append((a, p, q))
    common_c = math.lcm(*(z.denominator for z in cf))
    ci = [z.numerator*(common_c//z.denominator) for z in cf]
    rows = []
    for a, p, q in data:
        common = math.lcm(*(z.denominator for z in a+p))
        ai, pi = [[z.numerator*(common//z.denominator) for z in row] for row in (a, p)]
        rows.append((ai, pi, q.numerator, q.denominator, common))
    scale = 1 << precision
    minimum = None
    for vertex, label in enumerate(labels):
        indices = [i for i in range(n) if (vertex >> i) & 1]
        lo = scale*(ci[0]+sum(ci[i+1] for i in indices))//common_c
        for a, p, qn, qd, common in rows:
            av = sum(a[i] for i in indices)
            t1 = sum(p[i] for i in indices)
            t0 = sum(p)-t1
            numerator = av*qn*qd*(t1-t0)
            denominator = common*(qn+qd)*(qn*t1+qd*t0)
            assert denominator > 0
            lo += scale*numerator//denominator
        hi = lo+units+1
        signed = lo if label > 0 else -hi
        if signed <= 0:
            return None, {"certified": False, "reason": "shared-affine prelift interval",
                          "vertex": vertex}
        minimum = signed if minimum is None else min(minimum, signed)
    gamma = Fraction(minimum, scale)
    amplitude = sum((sum(map(abs, a)) for a, p, q in data if q == 1), Fraction(0))
    delta = dyadic_below(min(Fraction(1), gamma/(2*amplitude))) if amplitude else Fraction(1)
    heads, shared = [], cf.copy()
    zero_count = 0
    for a, p, q in data:
        if q == 1:
            q += delta
            zero_count += 1
        total = sum(p)
        numerator = [Fraction(0)]+[-z*q*total/(q-1) for z in a]
        denominator = [total]+[(q-1)*z for z in p]
        heads.append(rational_head(numerator, denominator, 1))
        for i, z in enumerate(a):
            shared[i+1] += 2*q*z/(q*q-1)
    heads.append(rational_head(shared, [Fraction(1)]+[Fraction(0)]*n, 1))
    cert = {"n": n, "labels": labels.astype(int).tolist(), "heads": heads, "bias": [0, 1],
            "scope": "This finite truth table only; no universal bound.",
            "shared_affine_lift": {"units": units, "zero_separation_units": zero_count,
                                    "zero_separation_perturbation": [delta.numerator, delta.denominator],
                                    "prelift_margin_lower_bound": [gamma.numerator, gamma.denominator]}}
    check = exact_check(cert, precision=precision)
    if not check["certified"]:
        return None, check
    cert["verification"] = check
    return cert, check


def initialize(checkpoint):
    saved = np.load(checkpoint)
    labels, logs, coef = saved["labels"], saved["logs"], saved["coefficients"]
    if "separation" in saved:
        return labels, logs, saved["separation"], coef
    assert "v" not in saved and "epsilon" not in saved, "Import ordinary heads only."
    ori = saved["orientation"]
    units, n = logs.shape
    slopes = np.exp(logs)
    total = slopes.sum(axis=1)
    separation = ori*.5*np.log1p(total)
    old_a = coef[1:].reshape(units, n)
    k0 = np.where(ori < 0, old_a.sum(axis=1)/(1+total), 0.)
    canonical = np.where(ori[:, None] > 0, old_a, -old_a+k0[:, None]*slopes)
    aa = -ori[:, None]*(total/(1+total))[:, None]*canonical
    cf = np.r_[coef[0]+k0.sum(), (2/(2+total)[:, None]*canonical).sum(axis=0)]
    # Center this scale-invariant parameter so the bounds do not clip its import.
    centered = logs-(logs.max(axis=1, keepdims=True)+logs.min(axis=1, keepdims=True))/2
    return labels, centered, separation, np.r_[cf, aa.ravel()]


class Problem:
    def __init__(self, labels, logs, separation, coefficient, out, seconds,
                 positive_only=False, inner_method="newton"):
        self.labels = labels
        self.units, self.n = logs.shape
        self.x = ((np.arange(len(labels))[:, None] >> np.arange(self.n)) & 1).astype(float)
        self.initial = np.r_[logs.ravel(), separation]
        self.previous, self.best = coefficient, None
        self.out, self.start = out, time.monotonic()
        self.deadline = self.start+seconds
        self.events, self.certificate = [], None
        self.positive_only = positive_only
        self.inner_method = inner_method
        if positive_only:
            assert np.all(separation > 0)

    def objective(self, parameters):
        if time.monotonic() >= self.deadline or (self.out/"STOP").exists():
            raise EndSearch
        logs, separation = unpack(parameters, self.units, self.n)
        feature = features(self.x, logs, separation)
        q, r = la.qr(feature, mode="economic", check_finite=False)
        initial = q.T@(feature@self.previous) if self.previous is not None else q.T@self.labels
        fit = convex_hinge_fit(self.labels[:, None]*q, initial, self.inner_method, 0.)
        coefficient = la.solve_triangular(r, fit.x, check_finite=False)
        self.previous = coefficient
        loss, score, gradient = score_gradient(self.x, self.labels, logs, separation, coefficient)
        event = {"evaluation": len(self.events), "seconds": time.monotonic()-self.start,
                 "loss": loss, "errors": int((self.labels*score <= 0).sum()),
                 "minimum_margin": float((self.labels*score).min()),
                 "inner_gradient": float(np.max(np.abs(fit.jac))),
                 "inner_iterations": int(fit.nit),
                 "inner_method": self.inner_method,
                 "direct_qr_score_discrepancy": float(np.max(np.abs(score-q@fit.x))),
                 "outer_gradient_norm": float(la.norm(gradient)),
                 "negative_units": int((separation < 0).sum()),
                 "minimum_absolute_separation": float(np.min(np.abs(separation)))}
        self.events.append(event)
        print(json.dumps(event), flush=True)
        if self.best is None or loss < self.best[0]:
            self.best = (loss, parameters.copy(), coefficient.copy())
            np.savez(self.out/"checkpoint.npz", labels=self.labels, logs=logs,
                     separation=separation, coefficients=coefficient, kind="shared-affine")
        if event["minimum_margin"] > 1e-5:
            cert, check = exact_lift(self.labels, logs, separation, coefficient)
            event["exact_check"] = check
            if cert is not None:
                (self.out/"certificate.json").write_text(json.dumps(cert)+"\n")
                self.certificate = "certificate.json"
                raise EndSearch
        return loss, gradient

    def run(self):
        try:
            result = opt.minimize(self.objective, self.initial, jac=True, method="L-BFGS-B",
                                  bounds=[(-70, 70)]*(self.units*self.n)+
                                  ([(1e-8, 35)] if self.positive_only else [(-35, 35)])*self.units,
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
                  "scope": "Finite orientation-crossing search; no universal theorem.",
                  "failure_is_not_a_lower_bound": True}
        result["positive_orientation_only"] = self.positive_only
        result["inner_method"] = self.inner_method
        (self.out/"result.json").write_text(json.dumps(result)+"\n")
        print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


def self_test(inner_method="newton"):
    rng = np.random.default_rng(2026112201)
    n, units = 5, 2
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    logs = rng.normal(size=(units, n))
    coef = rng.normal(0, .1, n+1+n*units)
    labels = rng.choice([-1., 1.], len(x))
    records, last = [], None
    for separation in (np.array([.6, -.8]), np.zeros(units), np.array([0., -.8])):
        params = np.r_[logs.ravel(), separation]
        loss, score, grad = score_gradient(x, labels, logs, separation, coef)
        numeric = []
        for i in range(len(params)):
            step = np.zeros_like(params)
            step[i] = 1e-5
            plus = score_gradient(x, labels, *unpack(params+step, units, n), coef)[0]
            minus = score_gradient(x, labels, *unpack(params-step, units, n), coef)[0]
            numeric.append((plus-minus)/2e-5)
        error = float(np.max(np.abs(grad-numeric)))
        assert error < 1e-8, error
        assert abs(geometry(x, logs, separation)[-1]).max() <= 1
        strict = np.where(score > 0, 1., -1.)
        cert, check = exact_lift(strict, logs, separation, coef)
        assert cert is not None, check
        records.append({"separation": separation.tolist(), "fixed_gradient_error": error,
                        "exact_check": check})
        last = cert
    separation = np.array([.6, -.8])
    def refit(parameters):
        ll, ss = unpack(parameters, units, n)
        feature = features(x, ll, ss)
        q, r = la.qr(feature, mode="economic")
        fit = convex_hinge_fit(labels[:, None]*q, q.T@labels, inner_method, 0.)
        cc = la.solve_triangular(r, fit.x)
        return score_gradient(x, labels, ll, ss, cc)
    params = np.r_[logs.ravel(), separation]
    _, _, grad = refit(params)
    numeric = []
    for i in range(len(params)):
        step = np.zeros_like(params)
        step[i] = 1e-5
        numeric.append((refit(params+step)[0]-refit(params-step)[0])/2e-5)
    refit_error = float(np.max(np.abs(grad-numeric)))
    assert refit_error < 1e-6, refit_error
    orientation = np.array([-1, 1])
    ordinary = rng.normal(size=1+units*n)
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    old_score = ordinary[0]+(np.einsum("xhi,hi->xh", t, ordinary[1:].reshape(units, n))/
                             (1+np.einsum("xhi,hi->xh", t, np.exp(logs)))).sum(axis=1)
    with TemporaryDirectory() as directory:
        checkpoint = Path(directory)/"ordinary.npz"
        np.savez(checkpoint, labels=labels, orientation=orientation, logs=logs,
                 coefficients=ordinary)
        _, imported_logs, imported_s, imported_coef = initialize(checkpoint)
        new_score = score_gradient(x, labels, imported_logs, imported_s, imported_coef)[1]
    import_error = float(np.max(np.abs(old_score-new_score)))
    assert import_error < 1e-12, import_error
    constant = {"n": 1, "labels": [-1, 1], "bias": [0, 1],
                "heads": [{"numerator": [-1, 2], "denominator": [1, 0]}]}
    assert exact_check(constant)["certified"]
    mixed = {"n": 2, "labels": [1]*4, "bias": [0, 1],
             "heads": [{"numerator": [1, 0, 0], "denominator": [2, 1, 0]}]}
    assert not exact_check(mixed)["certified"]
    return {"tests": records, "refitted_gradient_error": refit_error,
            "inner_method": inner_method,
            "ordinary_import_score_error": import_error,
            "constant_denominator_regression": "passed",
            "mixed_zero_slope_rejection": "passed",
            "scope": "Finite derivative and exact-export diagnostics only."}, last


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", nargs="?", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--positive-only", action="store_true")
    parser.add_argument("--inner-method", choices=("newton", "newton_cg", "lbfgs"),
                        default="newton")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.self_test:
        result, cert = self_test(args.inner_method)
        (args.out/"diagnostic.json").write_text(json.dumps(result, indent=2)+"\n")
        (args.out/"certificate.json").write_text(json.dumps(cert)+"\n")
        print(json.dumps(result), flush=True)
    else:
        assert args.checkpoint is not None
        Problem(*initialize(args.checkpoint), args.out, args.seconds,
                positive_only=args.positive_only, inner_method=args.inner_method).run()
