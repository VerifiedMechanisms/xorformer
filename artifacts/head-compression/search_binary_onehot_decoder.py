#!/usr/bin/env python3
"""Probe affine-ratio decoding on binary addresses and one-hot selectors.

Denominators are admissible on the full cube, but labels are prescribed only
on the promised subset. A success is not a full-cube theorem. Run with heavy.
"""
import argparse
from fractions import Fraction
import json
import math
import os
from pathlib import Path
import time

for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
from search_varpro_scores import convex_hinge_fit, TimeLimit, Certified
from search_newton_scores import export


def verify_promised(data):
    n = data["n"]
    vertices = data["vertices"]
    assert len(vertices) == len(data["labels"])
    assert len(set(vertices)) == len(vertices)
    for h in data["heads"]:
        a, b = h["numerator"], h["denominator"]
        assert len(a) == len(b) == n + 1
        assert all(isinstance(v, int) for v in a + b)
        assert all(v > 0 for v in b[1:])
        assert b[0] > 0
    least = None
    for x, y in zip(vertices, data["labels"]):
        assert 0 <= x < 1 << n and y in (-1, 1)
        indices = [i + 1 for i in range(n) if x >> i & 1]
        score = Fraction(*data["bias"])
        for h in data["heads"]:
            a, b = h["numerator"], h["denominator"]
            score += Fraction(a[0] + sum(a[i] for i in indices),
                              b[0] + sum(b[i] for i in indices))
        margin = y * score
        if margin <= 0:
            return {"certified": False, "vertex": x}
        least = margin if least is None else min(least, margin)
    return {"certified": True, "vertices_checked": len(vertices),
            "margin_approximation": float(least),
            "scope": "Promised subset only. Admissibility holds on full cube."}


class Decoder:
    def __init__(self, k, selectors, heads, seed, seconds, out):
        self.k, self.d, self.h = k, selectors, heads
        self.n, self.seed, self.out = k + selectors, seed, out
        self.rng = np.random.default_rng(seed)
        self.vertices = np.array([a | (1 << (k + j))
                                  for j in range(selectors) for a in range(1 << k)])
        self.x = ((self.vertices[:, None] >> np.arange(self.n)) & 1).astype(float)
        self.y = self.rng.choice([-1., 1.], len(self.x))
        self.start = time.monotonic()
        self.deadline = self.start + seconds
        self.penalty = 1e-7
        self.previous = None
        self.best_loss = math.inf
        self.best_errors = len(self.x)
        self.evaluations = 0
        self.last_log = self.start
        self.certificate = None

    def objective(self, logs, certify=True):
        if time.monotonic() >= self.deadline:
            raise TimeLimit
        b = np.exp(logs.reshape(self.h, self.n))
        den = 1 + self.x @ b.T
        # On the promise sum(selector bits)=1. One numerator coordinate
        # per head is redundant after including the shared constant.
        features = np.column_stack((np.ones(len(self.x)),
                    (self.x[:, None, :-1] / den[:, :, None]).reshape(len(self.x), -1)))
        q, r = la.qr(features, mode="economic", check_finite=False)
        z0 = q.T @ (features @ self.previous) if self.previous is not None else q.T @ self.y
        fit = convex_hinge_fit(self.y[:, None] * q, z0, "newton", self.penalty)
        coeff = la.solve_triangular(r, fit.x, check_finite=False)
        self.previous = coeff
        score = q @ fit.x
        residual = np.maximum(1 - self.y * score, 0)
        loss = (.5 * residual @ residual + .5 * self.penalty * (score @ score)) / len(self.x)
        u = np.column_stack((coeff[1:].reshape(self.h, self.n - 1), np.zeros(self.h)))
        numerator = self.x @ u.T
        weights = self.y * residual - self.penalty * score
        gradient = np.einsum("x,xh,xi,hi->hi", weights, numerator / den**2,
                             self.x, b) / len(self.x)
        errors = int(np.count_nonzero(self.y * score <= 0))
        self.best_errors = min(self.best_errors, errors)
        self.evaluations += 1
        if loss < self.best_loss:
            self.best_loss, self.best_logs = float(loss), logs.copy()
            np.savez(self.out / "checkpoint.npz", logs=logs, coefficients=coeff,
                     vertices=self.vertices, labels=self.y, k=self.k, selectors=self.d)
        if time.monotonic() - self.last_log > 30:
            print(json.dumps({"k": self.k, "selectors": self.d, "heads": self.h,
                "seed": self.seed, "seconds": time.monotonic() - self.start,
                "loss": float(loss), "errors": errors,
                "inner_gradient": float(np.max(np.abs(fit.jac))),
                "score_discrepancy": float(np.max(np.abs(features @ coeff - score)))}), flush=True)
            self.last_log = time.monotonic()
        if certify and np.min(self.y * score) > 1e-6:
            cert = export(self.n, self.y, u, b, np.ones(self.h), coeff[0])
            cert["vertices"] = self.vertices.tolist()
            cert["scope"] = "Binary-address, one-hot-selector promise only; no full-cube upper bound."
            cert["verification"] = verify_promised(cert)
            if cert["verification"]["certified"]:
                self.certificate = str(self.out / "certificate.json")
                Path(self.certificate).write_text(json.dumps(cert) + "\n")
                raise Certified
        return float(loss), gradient.ravel()

    def run(self):
        restarts = 0
        try:
            while time.monotonic() < self.deadline:
                logs = self.rng.normal(0, 2, self.h * self.n)
                if restarts and self.best_errors < len(self.x) // 4:
                    logs = self.best_logs + self.rng.normal(0, .5, logs.shape)
                self.previous = None
                opt.minimize(self.objective, logs, jac=True, method="L-BFGS-B",
                             bounds=[(-20, 20)] * len(logs),
                             options={"maxiter": 100000, "gtol": 1e-10,
                                      "ftol": 1e-14, "maxls": 40, "maxcor": 30})
                restarts += 1
        except (TimeLimit, Certified):
            pass
        return {"k": self.k, "selectors": self.d, "heads": self.h,
                "seed": self.seed, "vertices": len(self.x),
                "seconds": time.monotonic() - self.start,
                "best_loss": self.best_loss, "best_errors": self.best_errors,
                "certificate": self.certificate, "restarts": restarts,
                "failure_is_not_a_lower_bound": True,
                "scope": "Promised subset only, not full Boolean cube."}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=7200)
    p.add_argument("--trial-seconds", type=float, default=900)
    p.add_argument("--seed", type=int, default=310000)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + args.seconds
    index = 0
    while time.monotonic() < deadline:
        k = (5, 6, 7, 8)[index % 4]
        heads = math.ceil((1 << k) / k)
        out = args.out / f"k{k}-d{k}-h{heads}-seed{args.seed + index}"
        out.mkdir(exist_ok=True)
        problem = Decoder(k, k, heads, args.seed + index,
                          min(args.trial_seconds, deadline - time.monotonic()), out)
        result = problem.run()
        (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps(result), flush=True)
        index += 1


if __name__ == "__main__":
    main()
