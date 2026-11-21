#!/usr/bin/env python3
"""Adaptive confluent pairs, with an exact two-head lift on strict success.

Search c+sum(C/B+U*V/B**2), with positive same-orientation affine B.
The rank-one quadratic terms are evaluated without subtracting close heads.
No assertion of global convergence or universal capacity is made. Use heavy.
"""
import argparse
from fractions import Fraction
import json
import math
import os
from pathlib import Path
import time

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
from search_varpro_scores import convex_hinge_fit
from search_sign_scores import exact_check


def dyadic_below(value):
    assert value > 0
    k = max(0, value.denominator.bit_length()-value.numerator.bit_length()+1)
    eps = Fraction(1, 1 << k)
    while eps > value:
        k += 1
        eps /= 2
    return eps


def common_integer_coefficients(*rows):
    fractions = [[Fraction(float(v)) for v in row] for row in rows]
    common = max(v.denominator for row in fractions for v in row)
    return [[v.numerator*(common//v.denominator) for v in row] for row in fractions]


def rational_head(a, b, orientation):
    a, b = list(a), list(b)
    if orientation < 0:
        a = [sum(a), *[-v for v in a[1:]]]
        b = [sum(b), *[-v for v in b[1:]]]
    scale = math.lcm(*(z.denominator for z in a+b))
    return {"numerator": [z.numerator*(scale//z.denominator) for z in a],
            "denominator": [z.numerator*(scale//z.denominator) for z in b]}


def certify_and_lift(labels, orientation, logs, v, coefficient, precision=192):
    """Integer interval check first, then a provably small exact perturbation."""
    units, n = logs.shape
    ccoef, ucoef = coefficient[1:].reshape(2, units, n)
    rows = [common_integer_coefficients(np.r_[0., ccoef[h]], np.r_[0., ucoef[h]],
                                        np.r_[0., v[h]], np.r_[1., np.exp(logs[h])])
            for h in range(units)]
    scale = 1 << precision
    bias = Fraction(float(coefficient[0]))
    minimum = None
    for vertex, label in enumerate(labels):
        lo = (scale*bias.numerator)//bias.denominator
        for (cc, uu, vv, bb), ori in zip(rows, orientation):
            indices = [i+1 for i in range(n) if ((vertex >> i) & 1) == (ori > 0)]
            cv, uv, value, bv = [a[0]+sum(a[i] for i in indices) for a in (cc, uu, vv, bb)]
            assert bv > 0
            lo += scale*(cv*bv+uv*value)//(bv*bv)
        hi = lo+units+1
        signed = lo if label > 0 else -hi
        if signed <= 0:
            return None, {"certified": False, "reason": "confluent margin interval", "vertex": vertex}
        minimum = signed if minimum is None else min(minimum, signed)
    gamma = Fraction(minimum, scale)
    bound = Fraction(1)
    amplitude = Fraction(0)
    for cc, uu, vv, bb in rows:
        assert bb[0] > 0 and all(b > 0 for b in bb[1:])
        assert cc[0] == uu[0] == vv[0] == 0
        amplitude += Fraction(sum(map(abs, uu))*sum(map(abs, vv))**2, bb[0]**3)
        for b, value in zip(bb[1:], vv[1:]):
            if value:
                bound = min(bound, Fraction(b, 2*abs(value)))
    if amplitude:
        bound = min(bound, gamma/(4*amplitude))
    epsilon = dyadic_below(bound)
    heads = []
    for (cc, uu, vv, bb), ori in zip(rows, orientation):
        a1 = [Fraction(c)+Fraction(u)/epsilon for c, u in zip(cc, uu)]
        a2 = [-Fraction(u)/epsilon for u in uu]
        b1 = list(map(Fraction, bb))
        b2 = [Fraction(b)+epsilon*value for b, value in zip(bb, vv)]
        heads.extend((rational_head(a1, b1, ori), rational_head(a2, b2, ori)))
    cert = {"n": n, "labels": labels.astype(int).tolist(), "heads": heads,
            "bias": [bias.numerator, bias.denominator],
            "scope": "This finite truth table only; no universal bound.",
            "confluent_lift": {"units": units,
                               "epsilon": [epsilon.numerator, epsilon.denominator],
                               "prelift_margin_lower_bound": [gamma.numerator, gamma.denominator]}}
    check = exact_check(cert, precision=precision)
    if not check["certified"]:
        return None, check
    cert["verification"] = check
    return cert, check


def feature_data(t, logs, v):
    slopes = np.exp(logs)
    denominator = 1+np.einsum("xhi,hi->xh", t, slopes)
    local = t/denominator[:, :, None]
    direction = np.einsum("xhi,hi->xh", local, v)
    features = np.column_stack((np.ones(len(t)), local.reshape(len(t), -1),
                               (local*direction[:, :, None]).reshape(len(t), -1)))
    return features, local, direction


def score_gradient(t, labels, logs, v, coefficient):
    features, local, direction = feature_data(t, logs, v)
    units, n = logs.shape
    cc, uu = coefficient[1:].reshape(2, units, n)
    linear = np.einsum("xhi,hi->xh", local, cc)
    udot = np.einsum("xhi,hi->xh", local, uu)
    quadratic = udot*direction
    score = coefficient[0]+(linear+quadratic).sum(axis=1)
    residual = np.maximum(1-labels*score, 0.)
    weight = labels*residual
    glog = np.einsum("x,xh,xhi,hi->hi", weight, linear+2*quadratic,
                     local, np.exp(logs))/len(t)
    gv = -np.einsum("x,xh,xhi->hi", weight, udot, local)/len(t)
    return float(residual@residual/(2*len(t))), score, np.r_[glog.ravel(), gv.ravel()]


class EndSearch(Exception):
    pass


class Problem:
    def __init__(self, labels, orientation, logs, v, coefficient, out, seconds):
        self.labels, self.orientation = labels, orientation
        self.units, self.n = logs.shape
        x = ((np.arange(len(labels))[:, None] >> np.arange(self.n)) & 1).astype(float)
        self.t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
        self.initial = np.r_[logs.ravel(), v.ravel()]
        self.previous = coefficient
        self.best = None
        self.out = out
        self.start = time.monotonic()
        self.deadline = self.start+seconds
        self.events = []
        self.certificate = None

    def objective(self, parameters):
        if time.monotonic() >= self.deadline:
            raise EndSearch
        logs, v = parameters.reshape(2, self.units, self.n)
        features, _, _ = feature_data(self.t, logs, v)
        q, r = la.qr(features, mode="economic", check_finite=False)
        initial = q.T@(features@self.previous) if self.previous is not None else q.T@self.labels
        fit = convex_hinge_fit(self.labels[:, None]*q, initial, "newton", 0.)
        coefficient = la.solve_triangular(r, fit.x, check_finite=False)
        self.previous = coefficient
        loss, score, gradient = score_gradient(self.t, self.labels, logs, v, coefficient)
        qr_score = q@fit.x
        event = {"evaluation": len(self.events), "seconds": time.monotonic()-self.start,
                 "loss": loss, "errors": int((self.labels*score <= 0).sum()),
                 "minimum_margin": float((self.labels*score).min()),
                 "inner_gradient": float(np.max(np.abs(fit.jac))),
                 "direct_qr_score_discrepancy": float(np.max(np.abs(score-qr_score))),
                 "outer_gradient_norm": float(la.norm(gradient))}
        self.events.append(event)
        print(json.dumps(event), flush=True)
        if self.best is None or loss < self.best[0]:
            self.best = (loss, parameters.copy(), coefficient.copy())
            np.savez(self.out/"checkpoint.npz", labels=self.labels, orientation=self.orientation,
                     logs=logs, v=v, coefficients=coefficient, kind="confluent")
        if event["minimum_margin"] > 1e-5:
            cert, result = certify_and_lift(self.labels, self.orientation, logs, v, coefficient)
            event["exact_check"] = result
            if cert is not None:
                (self.out/"certificate.json").write_text(json.dumps(cert)+"\n")
                self.certificate = "certificate.json"
                raise EndSearch
        return loss, gradient

    def run(self):
        try:
            result = opt.minimize(self.objective, self.initial, jac=True, method="L-BFGS-B",
                                  bounds=[(-35, 35)]*(self.units*self.n)+
                                         [(-100, 100)]*(self.units*self.n),
                                  options={"maxiter": 100000, "maxfun": 100000,
                                           "ftol": 1e-15, "gtol": 1e-10,
                                           "maxls": 30, "maxcor": 50})
            termination = str(result.message)
        except EndSearch:
            termination = "certificate" if self.certificate else "time budget"
        result = {"n": self.n, "confluent_units": self.units, "lifted_heads": 2*self.units,
                  "seconds": time.monotonic()-self.start, "termination": termination,
                  "best_loss": None if self.best is None else self.best[0],
                  "certificate": self.certificate, "events": self.events,
                  "scope": "Finite adaptive confluent search; no global or universal theorem.",
                  "failure_is_not_a_lower_bound": True}
        (self.out/"result.json").write_text(json.dumps(result)+"\n")
        print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


def initialize(checkpoint, seed=0):
    saved = np.load(checkpoint)
    labels = saved["labels"].astype(float)
    if "v" in saved:
        return labels, saved["orientation"], saved["logs"], saved["v"], saved["coefficients"]
    logs = saved["logs"]
    orientation = saved["orientation"]
    heads, n = logs.shape
    coefficient = saved["coefficients"]
    numerator = coefficient[1:].reshape(heads, n)
    rng = np.random.default_rng(seed)
    result = []
    for ori in (-1, 1):
        remaining = list(np.flatnonzero(orientation == ori))
        while remaining:
            if len(remaining) == 1:
                i = remaining.pop()
                result.append((ori, logs[i], rng.normal(size=n), numerator[i], np.zeros(n)))
                continue
            distance = la.norm(logs[remaining, None]-logs[None, remaining], axis=2)
            np.fill_diagonal(distance, np.inf)
            ii, jj = np.unravel_index(np.argmin(distance), distance.shape)
            i, j = remaining[ii], remaining[jj]
            b1, b2 = np.exp(logs[i]), np.exp(logs[j])
            v = (b2-b1)/2
            norm = float(la.norm(v))
            if norm < 1e-12:
                v = rng.normal(size=n)
                norm = float(la.norm(v))
                u = np.zeros(n)
            else:
                u = (numerator[i]-numerator[j])*norm
            result.append((ori, np.log((b1+b2)/2), v/norm,
                           numerator[i]+numerator[j], u))
            remaining.remove(i)
            remaining.remove(j)
    ori, ll, vv, cc, uu = zip(*result)
    return labels, np.array(ori), np.array(ll), np.array(vv), np.r_[coefficient[0], np.ravel(cc), np.ravel(uu)]


def self_test():
    rng = np.random.default_rng(20261121)
    n, units = 4, 2
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    orientation = np.array([-1, 1])
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    labels = rng.choice([-1., 1.], len(x))
    logs, v = rng.normal(size=(units, n)), rng.normal(size=(units, n))
    coefficient = rng.normal(0, .15, 1+2*units*n)
    loss, score, gradient = score_gradient(t, labels, logs, v, coefficient)
    parameters = np.r_[logs.ravel(), v.ravel()]
    numerical = []
    for i in range(len(parameters)):
        step = np.zeros_like(parameters)
        step[i] = 1e-5
        values = []
        for shift in (step, -step):
            ll, vv = (parameters+shift).reshape(2, units, n)
            values.append(score_gradient(t, labels, ll, vv, coefficient)[0])
        numerical.append((values[0]-values[1])/2e-5)
    error = float(np.max(np.abs(gradient-numerical)))
    assert error < 1e-8, error
    # Independently refit the linear coordinates at each finite-difference
    # point, on a parity instance that cannot have zero loss in one unit.
    parity = 1-2*(x.sum(axis=1) % 2)
    one_t, one_logs, one_v = t[:, :1], logs[:1], v[:1]
    def reduced(params):
        ll, vv = params.reshape(2, 1, n)
        features, _, _ = feature_data(one_t, ll, vv)
        q, r = la.qr(features, mode="economic")
        fit = convex_hinge_fit(parity[:, None]*q, q.T@parity, "newton", 0.)
        coef = la.solve_triangular(r, fit.x)
        return score_gradient(one_t, parity, ll, vv, coef)
    one_params = np.r_[one_logs.ravel(), one_v.ravel()]
    reduced_loss, _, reduced_grad = reduced(one_params)
    reduced_num = []
    for i in range(len(one_params)):
        step = np.zeros_like(one_params)
        step[i] = 1e-5
        reduced_num.append((reduced(one_params+step)[0]-reduced(one_params-step)[0])/2e-5)
    reduced_error = float(np.max(np.abs(reduced_grad-reduced_num)))
    assert reduced_loss > 0 and reduced_error < 1e-6, (reduced_loss, reduced_error)
    assert np.min(np.abs(score)) > 1e-8
    strict_labels = np.where(score > 0, 1., -1.)
    cert, audit = certify_and_lift(strict_labels, orientation, logs, v, coefficient)
    assert cert is not None, audit
    return {"fixed_coefficient_gradient_max_error": error,
            "reduced_gradient_max_error": reduced_error,
            "positive_reduced_test_loss": reduced_loss, "exact_lift_check": audit,
            "lift_epsilon": cert["confluent_lift"]["epsilon"],
            "scope": "Derivative diagnostic and one finite exact lift, not a universal theorem."}, cert


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
        Problem(*initialize(args.checkpoint), args.out, args.seconds).run()
