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

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import mpmath as mp
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
from scipy.special import exprel
from search_confluent_varpro import dyadic_below, rational_head, EndSearch
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


def score_gradient(t, labels, logs, w, eps, coefficient):
    _, (b1, b2, v, l1, l2, v2) = features_and_geometry(t, logs, w, eps)
    units, n = logs.shape
    cc, uu = coefficient[1:].reshape(2, units, n)
    linear = np.einsum("xhi,hi->xh", l1, cc)
    u1, u2 = [np.einsum("xhi,hi->xh", local, uu) for local in (l1, l2)]
    quadratic = u1*v2
    score = coefficient[0]+(linear+quadratic).sum(axis=1)
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


def exact_lift(labels, orientation, logs, w, eps, coefficient, precision=224):
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
    minimum = None
    for vertex, label in enumerate(labels):
        lo = scale*bias.numerator//bias.denominator
        for rows, ori in zip(integer_rows, orientation):
            indices = [i+1 for i in range(n) if ((vertex >> i) & 1) == (ori > 0)]
            c, u, v, b1, b2 = [a[0]+sum(a[i] for i in indices) for a in rows]
            assert b1 > 0 and b2 > 0
            lo += scale*(c*b2+u*v)//(b1*b2)
        hi = lo+units+1
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
    cert = {"n": n, "labels": labels.astype(int).tolist(), "heads": heads,
            "bias": [bias.numerator, bias.denominator],
            "scope": "This finite truth table only; no universal bound.",
            "stable_pair_lift": {"units": units, "zero_epsilon_units": int((eps == 0).sum()),
                                 "zero_epsilon_perturbation": [delta.numerator, delta.denominator],
                                 "prelift_margin_lower_bound": [gamma.numerator, gamma.denominator]}}
    check = exact_check(cert, precision=precision)
    if not check["certified"]:
        return None, check
    cert["verification"] = check
    return cert, check


class Problem:
    def __init__(self, labels, orientation, logs, w, eps, coefficient, out, seconds):
        self.labels, self.orientation = labels, orientation
        self.units, self.n = logs.shape
        x = ((np.arange(len(labels))[:, None] >> np.arange(self.n)) & 1).astype(float)
        self.t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
        self.initial = np.r_[logs.ravel(), w.ravel(), eps]
        self.previous = coefficient
        self.best = None
        self.out = out
        self.start = time.monotonic()
        self.deadline = self.start+seconds
        self.events, self.certificate = [], None

    def objective(self, parameters):
        if time.monotonic() >= self.deadline or (self.out/"STOP").exists():
            raise EndSearch
        logs, w, eps = unpack(parameters, self.units, self.n)
        features, _ = features_and_geometry(self.t, logs, w, eps)
        q, r = la.qr(features, mode="economic", check_finite=False)
        initial = q.T@(features@self.previous) if self.previous is not None else q.T@self.labels
        fit = convex_hinge_fit(self.labels[:, None]*q, initial, "newton", 0.)
        coefficient = la.solve_triangular(r, fit.x, check_finite=False)
        self.previous = coefficient
        loss, score, gradient = score_gradient(self.t, self.labels, logs, w, eps, coefficient)
        event = {"evaluation": len(self.events), "seconds": time.monotonic()-self.start,
                 "loss": loss, "errors": int((self.labels*score <= 0).sum()),
                 "minimum_margin": float((self.labels*score).min()),
                 "inner_gradient": float(np.max(np.abs(fit.jac))),
                 "direct_qr_score_discrepancy": float(np.max(np.abs(score-q@fit.x))),
                 "outer_gradient_norm": float(la.norm(gradient)),
                 "minimum_absolute_epsilon": float(np.min(np.abs(eps)))}
        self.events.append(event)
        print(json.dumps(event), flush=True)
        if self.best is None or loss < self.best[0]:
            self.best = (loss, parameters.copy(), coefficient.copy())
            np.savez(self.out/"checkpoint.npz", labels=self.labels, orientation=self.orientation,
                     logs=logs, w=w, epsilon=eps, coefficients=coefficient, kind="stable-pair")
        if event["minimum_margin"] > 1e-5:
            cert, result = exact_lift(self.labels, self.orientation, logs, w, eps, coefficient)
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
                                         [(-70, 70)]*(self.units*self.n)+[(-1, 1)]*self.units,
                                  options={"maxiter": 100000, "maxfun": 100000,
                                           "ftol": 1e-15, "gtol": 1e-10,
                                           "maxls": 35, "maxcor": 50})
            termination = str(result.message)
        except EndSearch:
            termination = "certificate" if self.certificate else "budget or stop file"
        result = {"n": self.n, "units": self.units, "lifted_heads": 2*self.units,
                  "seconds": time.monotonic()-self.start, "termination": termination,
                  "best_loss": None if self.best is None else self.best[0],
                  "certificate": self.certificate, "events": self.events,
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
        return labels, ori, logs, saved["v"]/np.exp(logs), np.zeros(len(logs)), coef
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
    return {"tests": records, "scope": "Finite derivative and exact-export diagnostics only."}, last


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
