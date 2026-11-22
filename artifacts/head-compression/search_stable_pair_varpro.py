#!/usr/bin/env python3
"""Stable ordinary and confluent head pairs in one adaptive search chart.

B1=1+b.t, B2=1+sum(b_i exp(e*w_i)t_i),
V_i=b_i*w_i*exprel(e*w_i), and S=C/B1+U*V/(B1*B2).
At e=0 the chart includes the confluent limit. Every strict success is
converted to ordinary admissible heads and checked with exact integers.
This is a finite heuristic, not a universal construction. Use heavy.
"""
import argparse
from fractions import Fraction
import json
import math
import os
from pathlib import Path
import time
from tempfile import TemporaryDirectory

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import mpmath as mp
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
from scipy.special import exprel
from search_confluent_varpro import (dyadic_below, rational_head, EndSearch,
                                    score_gradient as confluent_score)
from search_sign_scores import exact_check
from search_varpro_scores import convex_hinge_fit


def exprel_prime(z):
    result = np.empty_like(z)
    small = np.abs(z) < .05
    result[small] = sum((k+1)*z[small]**k/math.factorial(k+2) for k in range(9))
    zz = z[~small]
    result[~small] = ((zz-1)*np.exp(zz)+1)/(zz*zz)
    return result


def unpack(parameters, units, n):
    split = units*n
    return (parameters[:split].reshape(units, n),
            parameters[split:2*split].reshape(units, n), parameters[2*split:])


def direction_coordinates(logs, w):
    """Rescale bounded w to coordinates with moderate initial magnitudes."""
    assert np.max(np.abs(w)) < 70.
    raw = 70*np.exp(logs)*np.arctanh(w/70)
    magnitude = np.max(np.abs(raw), axis=1)
    scale = np.ones(len(logs))
    nonzero = magnitude > 0
    scale[nonzero] = np.exp2(np.floor(np.log2(32/magnitude[nonzero])))
    return scale, raw*scale[:, None]


def bounded_direction(logs, direction, scale):
    """Return w and its diagonal derivatives at fixed direction or logs."""
    denominator = scale[:, None]*np.exp(logs)
    z = direction/(70*denominator)
    value = np.tanh(z)
    slope = 1-value*value
    return 70*value, -70*z*slope, slope/denominator


def features_and_geometry(t, logs, w, eps):
    b1 = np.exp(logs)
    z = eps[:, None]*w
    b2 = b1*np.exp(z)
    v = b1*w*exprel(z)
    d1 = 1+np.einsum("xhi,hi->xh", t, b1)
    d2 = 1+np.einsum("xhi,hi->xh", t, b2)
    l1, l2 = t/d1[:, :, None], t/d2[:, :, None]
    v2 = np.einsum("xhi,hi->xh", l2, v)
    features = np.column_stack((np.ones(len(t)), l1.reshape(len(t), -1),
                                (l1*v2[:, :, None]).reshape(len(t), -1)))
    return features, (b1, b2, v, l1, l2, v2)


def score_gradient(t, labels, logs, w, eps, coefficient, affine=None, x=None):
    _, (b1, b2, v, l1, l2, v2) = features_and_geometry(t, logs, w, eps)
    units, n = logs.shape
    cc, uu = coefficient[1:].reshape(2, units, n)
    linear = np.einsum("xhi,hi->xh", l1, cc)
    u1, u2 = [np.einsum("xhi,hi->xh", local, uu) for local in (l1, l2)]
    quadratic = u1*v2
    score = coefficient[0]+(linear+quadratic).sum(axis=1)
    if affine is not None:
        assert x is not None
        score = score+x@affine
    residual = np.maximum(1-labels*score, 0.)
    weight = -labels*residual/len(t)
    jlog = (-linear[:, :, None]*b1[None]*l1+u2[:, :, None]*v[None]*l1
            -quadratic[:, :, None]*(b1[None]*l1+b2[None]*l2))
    jw = u2[:, :, None]*b2[None]*l2
    veps = b1*w*w*exprel_prime(eps[:, None]*w)
    jeps = (u2*np.einsum("xhi,hi->xh", l1, veps)
            -quadratic*np.einsum("xhi,hi->xh", l2, b2*w))
    grad = np.r_[np.einsum("x,xhi->hi", weight, jlog).ravel(),
                 np.einsum("x,xhi->hi", weight, jw).ravel(), weight@jeps]
    return float(residual@residual/(2*len(t))), score, grad


def exact_lift(labels, orientation, logs, w, eps, coefficient, precision=224, affine=None):
    units, n = logs.shape
    cc, uu = coefficient[1:].reshape(2, units, n)
    data = []
    for h in range(units):
        e = Fraction(float(eps[h]))
        digits = max(120, int(-math.log10(abs(float(e))))+120) if e else 120
        with mp.workdps(digits):
            b1 = [Fraction(1)]+[Fraction(str(mp.exp(mp.mpf(float(z))))) for z in logs[h]]
            b2 = [Fraction(1)]+[Fraction(str(mp.exp(mp.mpf(float(z))+
                                                    mp.mpf(float(eps[h]))*mp.mpf(float(ww)))))
                               for z, ww in zip(logs[h], w[h])]
        v = [(d-b)/e for b, d in zip(b1, b2)] if e else [Fraction(0)]+[
            b*Fraction(float(ww)) for b, ww in zip(b1[1:], w[h])]
        c = [Fraction(0)]+list(map(lambda z: Fraction(float(z)), cc[h]))
        u = [Fraction(0)]+list(map(lambda z: Fraction(float(z)), uu[h]))
        data.append((c, u, v, b1, b2, e))
    integer_rows = []
    for c, u, v, b1, b2, e in data:
        common = math.lcm(*(z.denominator for a in (c, u, v, b1, b2) for z in a))
        integer_rows.append([[z.numerator*(common//z.denominator) for z in a]
                             for a in (c, u, v, b1, b2)])
    scale = 1 << precision
    bias = Fraction(float(coefficient[0]))
    affine_rational = None if affine is None else [Fraction(float(z)) for z in affine]
    minimum = None
    for vertex, label in enumerate(labels):
        lo = scale*bias.numerator//bias.denominator
        if affine_rational is not None:
            av = sum((z for i, z in enumerate(affine_rational) if (vertex >> i) & 1), Fraction(0))
            lo += scale*av.numerator//av.denominator
        for rows, ori in zip(integer_rows, orientation):
            indices = [i+1 for i in range(n) if ((vertex >> i) & 1) == (ori > 0)]
            c, u, v, b1, b2 = [a[0]+sum(a[i] for i in indices) for a in rows]
            assert b1 > 0 and b2 > 0
            lo += scale*(c*b2+u*v)//(b1*b2)
        hi = lo+units+1+(affine_rational is not None)
        signed = lo if label > 0 else -hi
        if signed <= 0:
            return None, {"certified": False, "reason": "stable-pair interval", "vertex": vertex}
        minimum = signed if minimum is None else min(minimum, signed)
    gamma = Fraction(minimum, scale)
    bound, amplitude = Fraction(1), Fraction(0)
    for c, u, v, b1, b2, e in data:
        if not e:
            amplitude += sum(map(abs, u))*sum(map(abs, v))**2/b1[0]**3
            for b, value in zip(b1[1:], v[1:]):
                if value:
                    bound = min(bound, b/(2*abs(value)))
    if amplitude:
        bound = min(bound, gamma/(4*amplitude))
    delta = dyadic_below(bound)
    heads = []
    for (c, u, v, b1, b2, e), ori in zip(data, orientation):
        if not e:
            e = delta
            b2 = [b+e*value for b, value in zip(b1, v)]
        a1, a2 = [a+value/e for a, value in zip(c, u)], [-value/e for value in u]
        heads.extend((rational_head(a1, b1, ori), rational_head(a2, b2, ori)))
    if affine_rational is not None:
        heads.append(rational_head([Fraction(0)]+affine_rational,
                                   [Fraction(1)]+[Fraction(0)]*n, 1))
    cert = {"n": n, "labels": labels.astype(int).tolist(), "heads": heads,
            "bias": [bias.numerator, bias.denominator],
            "scope": "This finite truth table only; no universal bound.",
            "stable_pair_lift": {"units": units, "zero_epsilon_units": int((eps == 0).sum()),
                                 "affine_correction_heads": int(affine is not None),
                                 "zero_epsilon_perturbation": [delta.numerator, delta.denominator],
                                 "prelift_margin_lower_bound": [gamma.numerator, gamma.denominator]}}
    check = exact_check(cert, precision=precision)
    if not check["certified"]:
        return None, check
    cert["verification"] = check
    return cert, check


class Problem:
    def __init__(self, labels, orientation, logs, w, eps, coefficient, out, seconds,
                 scaled_direction=False, affine_correction=False):
        self.labels, self.orientation = labels, orientation
        self.units, self.n = logs.shape
        x = ((np.arange(len(labels))[:, None] >> np.arange(self.n)) & 1).astype(float)
        self.x, self.affine_correction = x, affine_correction
        self.pair_coefficient_count = 1+2*self.units*self.n
        if affine_correction and len(coefficient) == self.pair_coefficient_count:
            coefficient = np.r_[coefficient, np.zeros(self.n)]
        assert len(coefficient) == self.pair_coefficient_count+int(affine_correction)*self.n
        self.t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
        self.scaled_direction = scaled_direction
        if scaled_direction:
            self.direction_scale, direction = direction_coordinates(logs, w)
        else:
            self.direction_scale, direction = None, w
        self.initial = np.r_[logs.ravel(), direction.ravel(), eps]
        self.previous = coefficient
        self.best = None
        self.out = out
        self.start = time.monotonic()
        self.deadline = self.start+seconds
        self.events, self.certificate = [], None

    def objective(self, parameters):
        if time.monotonic() >= self.deadline or (self.out/"STOP").exists():
            raise EndSearch
        logs, direction, eps = unpack(parameters, self.units, self.n)
        if self.scaled_direction:
            w, dlog, ddirection = bounded_direction(logs, direction, self.direction_scale)
        else:
            w = direction
        features, _ = features_and_geometry(self.t, logs, w, eps)
        if self.affine_correction:
            features = np.column_stack((features, self.x))
        q, r = la.qr(features, mode="economic", check_finite=False)
        initial = q.T@(features@self.previous) if self.previous is not None else q.T@self.labels
        fit = convex_hinge_fit(self.labels[:, None]*q, initial, "newton", 0.)
        coefficient = la.solve_triangular(r, fit.x, check_finite=False)
        self.previous = coefficient
        pair_coefficient = coefficient[:self.pair_coefficient_count]
        affine = coefficient[self.pair_coefficient_count:] if self.affine_correction else None
        loss, score, gradient = score_gradient(self.t, self.labels, logs, w, eps,
                                               pair_coefficient, affine, self.x)
        if self.scaled_direction:
            gl, gw, ge = unpack(gradient, self.units, self.n)
            gradient = np.r_[(gl+gw*dlog).ravel(), (gw*ddirection).ravel(), ge]
        event = {"evaluation": len(self.events), "seconds": time.monotonic()-self.start,
                 "loss": loss, "errors": int((self.labels*score <= 0).sum()),
                 "minimum_margin": float((self.labels*score).min()),
                 "inner_gradient": float(np.max(np.abs(fit.jac))),
                 "direct_qr_score_discrepancy": float(np.max(np.abs(score-q@fit.x))),
                 "outer_gradient_norm": float(la.norm(gradient)),
                 "scaled_direction": self.scaled_direction,
                 "affine_correction_heads": int(self.affine_correction),
                 "minimum_absolute_epsilon": float(np.min(np.abs(eps)))}
        self.events.append(event)
        print(json.dumps(event), flush=True)
        if self.best is None or loss < self.best[0]:
            self.best = (loss, parameters.copy(), coefficient.copy())
            np.savez(self.out/"checkpoint.npz", labels=self.labels, orientation=self.orientation,
                     logs=logs, w=w, epsilon=eps, coefficients=coefficient,
                     kind="stable-pair-affine" if self.affine_correction else "stable-pair")
        if event["minimum_margin"] > 1e-5:
            cert, result = exact_lift(self.labels, self.orientation, logs, w, eps,
                                      pair_coefficient, affine=affine)
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
                                         ([(-100, 100)] if self.scaled_direction else
                                          [(-70, 70)])*(self.units*self.n)+[(-1, 1)]*self.units,
                                  options={"maxiter": 100000, "maxfun": 100000,
                                           "ftol": 1e-15, "gtol": 1e-10,
                                           "maxls": 35, "maxcor": 50})
            termination = str(result.message)
        except EndSearch:
            termination = "certificate" if self.certificate else "budget or stop file"
        result = {"n": self.n, "units": self.units,
                  "lifted_heads": 2*self.units+int(self.affine_correction),
                  "seconds": time.monotonic()-self.start, "termination": termination,
                  "best_loss": None if self.best is None else self.best[0],
                  "certificate": self.certificate, "events": self.events,
                  "scaled_direction": self.scaled_direction,
                  "affine_correction_heads": int(self.affine_correction),
                  "scope": "Finite stable-pair search; no global or universal theorem.",
                  "failure_is_not_a_lower_bound": True}
        (self.out/"result.json").write_text(json.dumps(result)+"\n")
        print(json.dumps({k: v for k, v in result.items() if k != "events"}), flush=True)


def initialize(checkpoint):
    saved = np.load(checkpoint)
    labels, ori, logs, coef = saved["labels"], saved["orientation"], saved["logs"], saved["coefficients"]
    if "epsilon" in saved:
        return labels, ori, logs, saved["w"], saved["epsilon"], coef
    if "v" in saved:
        raw_w = saved["v"]/np.exp(logs)
        # At epsilon=0, (U,V) -> (scale*U,V/scale) preserves U*V/B^2.
        # Without this rescaling, L-BFGS-B can clip the imported w to its
        # bounds and silently destroy the warm-start score. Powers of two
        # avoid unnecessary floating-point error in the scale operations.
        exponent = np.maximum(0., np.ceil(np.log2(
                     np.maximum(np.max(np.abs(raw_w), axis=1)/35., 1.))))
        scale = np.exp2(exponent)
        adjusted = coef.copy()
        adjusted[1:].reshape(2, len(logs), logs.shape[1])[1] *= scale[:, None]
        return labels, ori, logs, raw_w/scale[:, None], np.zeros(len(logs)), adjusted
    heads, n = logs.shape
    a = coef[1:].reshape(heads, n)
    result = []
    rng = np.random.default_rng(20261121)
    for orientation in (-1, 1):
        remaining = list(np.flatnonzero(ori == orientation))
        while remaining:
            if len(remaining) == 1:
                i = remaining.pop()
                result.append((orientation, logs[i], rng.normal(0, .1, n), a[i], np.zeros(n)))
                continue
            distance = la.norm(logs[remaining, None]-logs[None, remaining], axis=2)
            np.fill_diagonal(distance, np.inf)
            ii, jj = np.unravel_index(np.argmin(distance), distance.shape)
            i, j = remaining[ii], remaining[jj]
            w = logs[j]-logs[i]
            if la.norm(w) < 1e-12:
                w, u = rng.normal(0, .1, n), np.zeros(n)
            else:
                u = -a[j]
            result.append((orientation, logs[i], w, a[i]+a[j], u))
            remaining.remove(i)
            remaining.remove(j)
    ori, ll, ww, cc, uu = zip(*result)
    return labels, np.array(ori), np.array(ll), np.array(ww), np.ones(len(ori)), np.r_[coef[0], np.ravel(cc), np.ravel(uu)]


def self_test():
    rng = np.random.default_rng(20261122)
    n, units = 4, 2
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    ori = np.array([-1, 1])
    t = np.where(ori[None, :, None] > 0, x[:, None], 1-x[:, None])
    logs, w = rng.normal(size=(units, n)), rng.normal(size=(units, n))
    coef = rng.normal(0, .2, 1+2*units*n)
    labels = rng.choice([-1., 1.], len(x))
    records = []
    affine_records = []
    last = None
    for eps in (np.ones(units), np.zeros(units), np.array([1e-9, -1e-7])):
        params = np.r_[logs.ravel(), w.ravel(), eps]
        loss, score, grad = score_gradient(t, labels, logs, w, eps, coef)
        numerical = []
        for i in range(len(params)):
            step = np.zeros_like(params)
            step[i] = 1e-5
            plus = score_gradient(t, labels, *unpack(params+step, units, n), coef)[0]
            minus = score_gradient(t, labels, *unpack(params-step, units, n), coef)[0]
            numerical.append((plus-minus)/2e-5)
        error = float(np.max(np.abs(grad-numerical)))
        assert error < 1e-8, (eps, error)
        assert np.min(np.abs(score)) > 1e-6
        strict = np.where(score > 0, 1., -1.)
        cert, check = exact_lift(strict, ori, logs, w, eps, coef)
        assert cert is not None, check
        records.append({"epsilon": eps.tolist(), "gradient_max_error": error, "exact_check": check})
        last = cert
        affine = rng.normal(0, .2, n)
        _, affine_score, affine_gradient = score_gradient(t, labels, logs, w, eps, coef, affine, x)
        affine_numerical = []
        for i in range(len(params)):
            step = np.zeros_like(params)
            step[i] = 1e-5
            plus = score_gradient(t, labels, *unpack(params+step, units, n), coef, affine, x)[0]
            minus = score_gradient(t, labels, *unpack(params-step, units, n), coef, affine, x)[0]
            affine_numerical.append((plus-minus)/2e-5)
        affine_error = float(np.max(np.abs(affine_gradient-affine_numerical)))
        assert affine_error < 1e-8, affine_error
        affine_labels = np.where(affine_score > 0, 1., -1.)
        affine_cert, affine_check = exact_lift(affine_labels, ori, logs, w, eps, coef, affine=affine)
        assert affine_cert is not None, affine_check
        assert len(affine_cert["heads"]) == 2*units+1
        affine_records.append({"epsilon": eps.tolist(), "gradient_max_error": affine_error,
                               "exact_check": affine_check, "heads": 2*units+1})
        last = affine_cert
    # Test the envelope derivative after an independent convex refit at every
    # perturbed point. One pair cannot sign-represent four-bit parity, so this
    # diagnostic has positive loss and does not pass because all derivatives
    # happen to vanish at an interpolating score.
    parity = 1-2*(x.sum(axis=1) % 2)
    one_t, one_logs, one_w = t[:, :1], logs[:1], w[:1]
    reduced_records = []
    for epsilon in (0., .7, -1e-7):
        def reduced(parameters):
            ll, ww, ee = unpack(parameters, 1, n)
            feature = features_and_geometry(one_t, ll, ww, ee)[0]
            q, r = la.qr(feature, mode="economic")
            fit = convex_hinge_fit(parity[:, None]*q, q.T@parity, "newton", 0.)
            coefficient = la.solve_triangular(r, fit.x)
            assert np.max(np.abs(fit.jac)) < 1e-8
            return score_gradient(one_t, parity, ll, ww, ee, coefficient)
        parameters = np.r_[one_logs.ravel(), one_w.ravel(), epsilon]
        value, _, gradient = reduced(parameters)
        numerical = []
        for i in range(len(parameters)):
            step = np.zeros_like(parameters)
            step[i] = 1e-5
            numerical.append((reduced(parameters+step)[0]-
                              reduced(parameters-step)[0])/2e-5)
        error = float(np.max(np.abs(gradient-numerical)))
        assert value > 0 and error < 1e-6, (epsilon, value, error)
        reduced_records.append({"epsilon": epsilon, "positive_loss": value,
                                "refitted_gradient_max_error": error})
    def reduced_affine(parameters):
        ll, ww, ee = unpack(parameters, 1, n)
        feature = np.column_stack((features_and_geometry(one_t, ll, ww, ee)[0], x))
        q, r = la.qr(feature, mode="economic")
        fit = convex_hinge_fit(parity[:, None]*q, q.T@parity, "newton", 0.)
        coefficient = la.solve_triangular(r, fit.x)
        assert np.max(np.abs(fit.jac)) < 1e-8
        return score_gradient(one_t, parity, ll, ww, ee, coefficient[:-n], coefficient[-n:], x)
    affine_reduced_records = []
    for epsilon in (0., .7, -1e-7):
        parameters = np.r_[one_logs.ravel(), one_w.ravel(), epsilon]
        value, _, gradient = reduced_affine(parameters)
        numerical = []
        for i in range(len(parameters)):
            step = np.zeros_like(parameters)
            step[i] = 1e-5
            numerical.append((reduced_affine(parameters+step)[0]-
                              reduced_affine(parameters-step)[0])/2e-5)
        error = float(np.max(np.abs(gradient-numerical)))
        assert value > 0 and error < 1e-6, (epsilon, value, error)
        affine_reduced_records.append({"epsilon": epsilon, "positive_loss": value,
                                       "refitted_gradient_max_error": error})
    # A small denominator slope makes the unscaled import exceed the
    # optimizer's w bounds. Check that the rescaled import preserves values.
    imported_logs = logs.copy()
    imported_logs[:, 0] = -30.
    direction = rng.normal(size=(units, n))
    old_score = confluent_score(t, labels, imported_logs, direction, coef)[1]
    with TemporaryDirectory() as directory:
        path = Path(directory)/"confluent.npz"
        np.savez(path, labels=labels, orientation=ori, logs=imported_logs,
                 v=direction, coefficients=coef)
        _, _, ll, ww, ee, cc = initialize(path)
        imported_score = score_gradient(t, labels, ll, ww, ee, cc)[1]
    discrepancy = float(np.max(np.abs(imported_score-old_score)))
    assert np.max(np.abs(ww)) <= 35.
    assert np.all(ee == 0.)
    assert discrepancy < 1e-12, discrepancy
    coordinate_scale, coordinates = direction_coordinates(logs, w)
    parameters = np.r_[logs.ravel(), coordinates.ravel(), [.4, -.3]]
    def transformed(parameters):
        ll, vv, ee = unpack(parameters, units, n)
        ww, jl, jv = bounded_direction(ll, vv, coordinate_scale)
        loss, score, gradient = score_gradient(t, labels, ll, ww, ee, coef)
        gl, gw, ge = unpack(gradient, units, n)
        return loss, score, np.r_[(gl+gw*jl).ravel(), (gw*jv).ravel(), ge]
    transformed_loss, transformed_score, transformed_gradient = transformed(parameters)
    original_score = score_gradient(t, labels, logs, w, np.array([.4, -.3]), coef)[1]
    coordinate_error = float(np.max(np.abs(transformed_score-original_score)))
    numerical = []
    for i in range(len(parameters)):
        step = np.zeros_like(parameters)
        step[i] = 1e-5
        numerical.append((transformed(parameters+step)[0]-
                          transformed(parameters-step)[0])/2e-5)
    coordinate_gradient_error = float(np.max(np.abs(transformed_gradient-numerical)))
    assert coordinate_error < 1e-12
    assert coordinate_gradient_error < 1e-8, coordinate_gradient_error
    return {"tests": records, "affine_correction_tests": affine_records,
            "refitted_gradient_tests": reduced_records,
            "affine_refitted_gradient_tests": affine_reduced_records,
            "rescaled_confluent_import": {
                "original_maximum_absolute_w": float(np.max(np.abs(direction/np.exp(imported_logs)))),
                "imported_maximum_absolute_w": float(np.max(np.abs(ww))),
                "maximum_score_discrepancy": discrepancy},
            "scaled_direction_coordinates": {"score_discrepancy": coordinate_error,
                "fixed_coefficient_gradient_error": coordinate_gradient_error},
            "scope": "Finite derivative and exact-export diagnostics only."}, last


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", nargs="?", type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--scaled-direction", action="store_true")
    parser.add_argument("--affine-correction", action="store_true",
                        help="Add and explicitly charge one shared affine head.")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.self_test:
        result, cert = self_test()
        (args.out/"diagnostic.json").write_text(json.dumps(result, indent=2)+"\n")
        (args.out/"certificate.json").write_text(json.dumps(cert)+"\n")
        print(json.dumps(result), flush=True)
    else:
        assert args.checkpoint is not None
        Problem(*initialize(args.checkpoint), args.out, args.seconds,
                scaled_direction=args.scaled_direction,
                affine_correction=args.affine_correction).run()
