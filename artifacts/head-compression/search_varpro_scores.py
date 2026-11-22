#!/usr/bin/env python3
"""Optimize denominators after solving the convex numerator problem.

QR changes coordinates only inside the fixed-denominator score space. Every
reported success still requires independent integer evaluation on the cube.
This is a mechanism probe, not an asymptotic or universal theorem. Use heavy.
"""
import argparse
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
import scipy.sparse.linalg as spla
from search_newton_scores import export
from search_sign_scores import exact_check


class TimeLimit(Exception):
    pass


class Certified(Exception):
    pass


def matrix_free_hinge_fit(yq, initial, score_penalty):
    """Convex squared hinge fit using active-set Hessian products.

    This only changes the numerical solver, not the represented score space.
    The returned gradient records the achieved inner stationarity.
    """
    def inner(z):
        residual = np.maximum(1-yq @ z, 0)
        return (.5*residual @ residual + .5*score_penalty*(z @ z),
                -(yq.T @ residual) + score_penalty*z)

    z = initial.copy()
    cg_steps = 0
    for iteration in range(80):
        value, gradient = inner(z)
        if np.max(np.abs(gradient)) < 1e-9:
            break
        qa = yq[(1-yq @ z) > 0]
        ridge = max(score_penalty, 1e-12)
        operator = spla.LinearOperator((len(z), len(z)),
                    matvec=lambda v: qa.T @ (qa @ v)+ridge*v)
        diagonal = np.einsum("ij,ij->j", qa, qa)+ridge
        preconditioner = spla.LinearOperator((len(z), len(z)),
                    matvec=lambda v: v/diagonal)
        def count_step(_):
            nonlocal cg_steps
            cg_steps += 1
        direction, info = spla.cg(operator, -gradient, M=preconditioner,
                                 rtol=1e-8, atol=1e-12, maxiter=250,
                                 callback=count_step)
        slope = gradient @ direction
        if info < 0 or not np.isfinite(slope) or slope >= 0:
            direction, slope = -gradient, -(gradient @ gradient)
        alpha = 1.
        accepted = False
        for _ in range(30):
            trial_value, trial_gradient = inner(z+alpha*direction)
            armijo = trial_value <= value+1e-4*alpha*slope
            # Near stationarity the loss decrease can be below one ulp.
            # A large gradient reduction still justifies the Newton step.
            roundoff = (trial_value <= value+16*np.finfo(float).eps*(1+abs(value))
                        and la.norm(trial_gradient) < .5*la.norm(gradient))
            if armijo or roundoff:
                accepted = True
                break
            alpha *= .5
        if not accepted:
            break
        z += alpha*direction
    value, gradient = inner(z)
    if np.max(np.abs(gradient)) > 1e-8:
        polish = opt.minimize(inner, z, jac=True, method="L-BFGS-B",
                              options={"gtol": 1e-10, "ftol": 1e-15,
                                       "maxiter": 2000, "maxls": 50,
                                       "maxcor": 60})
        z = polish.x
        value, gradient = inner(z)
    return opt.OptimizeResult(x=z, fun=value, jac=gradient, nit=iteration+1,
                              cg_steps=cg_steps,
                              success=np.max(np.abs(gradient)) <= 1e-7)


def convex_hinge_fit(yq, initial, method, score_penalty):
    """Numerator optimization in orthonormal coordinates."""
    if method == "newton_cg":
        return matrix_free_hinge_fit(yq, initial, score_penalty)
    def inner(z):
        residual = np.maximum(1-yq @ z, 0)
        return (.5*residual @ residual + .5*score_penalty*(z @ z),
                -(yq.T @ residual) + score_penalty*z)

    if method == "lbfgs":
        return opt.minimize(inner, initial, jac=True, method="L-BFGS-B",
                            options={"gtol": 1e-9, "ftol": 1e-14, "maxiter": 2000,
                                     "maxls": 40, "maxcor": 30})
    z = initial.copy()
    for iteration in range(500):
        residual = np.maximum(1-yq @ z, 0)
        value, gradient = inner(z)
        if np.max(np.abs(gradient)) < 1e-9:
            break
        active = residual > 0
        qa = yq[active]
        gram = qa.T @ qa
        gram.flat[::len(gram)+1] += max(score_penalty, 1e-12)
        try:
            direction = la.solve(gram, -gradient, assume_a="pos", check_finite=False)
        except la.LinAlgError:
            direction = la.lstsq(gram, -gradient, cond=1e-13,
                                 check_finite=False, lapack_driver="gelsy")[0]
        slope = gradient @ direction
        alpha = 1.
        for _ in range(30):
            trial_value = inner(z+alpha*direction)[0]
            if trial_value <= value+1e-4*alpha*slope:
                break
            alpha *= .5
        z += alpha*direction
    value, gradient = inner(z)
    if np.max(np.abs(gradient)) > 1e-8:
        # A time-limited Newton loop is not a stationary inner solution.
        # Polish before using the envelope derivative in the outer search.
        polish = opt.minimize(inner, z, jac=True, method="L-BFGS-B",
                              options={"gtol": 1e-10, "ftol": 1e-15,
                                       "maxiter": 10000, "maxls": 50,
                                       "maxcor": 60})
        z = polish.x
        value, gradient = inner(z)
    return opt.OptimizeResult(x=z, fun=value, jac=gradient, nit=iteration+1)


class Problem:
    def __init__(self, n, h, seed, seconds, out, label_kind, inner_method="newton",
                 score_penalty=1e-7, resume=False, initialization="independent"):
        self.n, self.h, self.seed, self.out = n, h, seed, out
        self.start = time.monotonic()
        self.deadline = self.start + seconds
        self.rng = np.random.default_rng(seed)
        self.x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
        if label_kind == "parity":
            self.y = 1 - 2 * (self.x.sum(1) % 2)
        elif label_kind == "bent":
            self.y = 1 - 2 * ((self.x[:, :n//2] * self.x[:, n//2:2*(n//2)]).sum(1) % 2)
        else:
            self.y = self.rng.choice([-1., 1.], len(self.x))
        self.orientation = self.rng.choice([-1, 1], h)
        self.initialization = initialization
        if initialization == "paired":
            self.orientation[1:2*(h//2):2] = self.orientation[:2*(h//2):2]
        self.t = np.where(self.orientation[None, :, None] > 0,
                          self.x[:, None, :], 1-self.x[:, None, :])
        self.previous = None
        self.best_loss = math.inf
        self.best_errors = len(self.x)
        self.evaluations = 0
        self.certificate = None
        self.events = []
        self.label_kind = label_kind
        self.last_log = self.start
        self.check_certificate = True
        self.inner_method = inner_method
        self.score_penalty = score_penalty
        self.resume = resume
        self.initial_logs = None

    def objective(self, logs):
        if time.monotonic() >= self.deadline:
            raise TimeLimit
        b = np.exp(logs.reshape(self.h, self.n))
        d = 1 + np.einsum("xhi,hi->xh", self.t, b)
        features = np.column_stack((np.ones(len(self.x)),
                                    (self.t / d[:, :, None]).reshape(len(self.x), -1)))
        q, r = la.qr(features, mode="economic", check_finite=False)
        # Each QR column is orthonormal. The convex loss has a well-scaled
        # Hessian even when the original feature coefficients nearly cancel.
        yq = self.y[:, None] * q
        z0 = q.T @ (features @ self.previous) if self.previous is not None else q.T @ self.y

        fit = convex_hinge_fit(yq, z0, self.inner_method, self.score_penalty)
        coeff = la.solve_triangular(r, fit.x, check_finite=False)
        self.previous = coeff
        s = q @ fit.x
        margin = self.y * s
        residual = np.maximum(1 - margin, 0)
        loss = (.5 * residual @ residual + .5*self.score_penalty*(s @ s)) / len(self.x)
        u = coeff[1:].reshape(self.h, self.n)
        num = np.einsum("xhi,hi->xh", self.t, u)
        # Envelope derivative; the inner numerator problem is convex.
        weights = self.y * residual - self.score_penalty*s
        grad = np.einsum("x,xh,xhi,hi->hi", weights, num / d**2, self.t, b) / len(self.x)
        self.evaluations += 1
        errors = int((margin <= 0).sum())
        self.best_errors = min(self.best_errors, errors)
        if loss < self.best_loss:
            self.best_loss = loss
            self.best_logs, self.best_coeff = logs.copy(), coeff.copy()
            np.savez(self.out / f"checkpoint-{self.label_kind}-n{self.n}-h{self.h}-seed{self.seed}.npz",
                     logs=logs, coefficients=coeff, orientation=self.orientation, labels=self.y)
        event = {"evaluation": self.evaluations, "seconds": time.monotonic()-self.start,
                 "loss": float(loss), "errors": errors, "min_margin": float(margin.min()),
                 "inner_gradient": float(np.linalg.norm(fit.jac, np.inf)),
                 "coefficient_max": float(np.max(np.abs(coeff))),
                 "score_discrepancy": float(np.max(np.abs(features @ coeff - s)))}
        self.events.append(event)
        if time.monotonic()-self.last_log >= 30:
            print(json.dumps({"progress": True, "n": self.n, "heads": self.h,
                              "seed": self.seed, **event}), flush=True)
            self.last_log = time.monotonic()
        if self.check_certificate and margin.min() > 1e-6:
            cert = export(self.n, self.y, u, b, self.orientation, coeff[0])
            check = exact_check(cert)
            if check["certified"]:
                self.certified_logs = logs.copy()
                self.certified_coeff = coeff.copy()
                cert["verification"] = check
                self.certificate = f"{self.label_kind}-n{self.n}-h{self.h}-seed{self.seed}.json"
                (self.out / self.certificate).write_text(json.dumps(cert)+"\n")
                raise Certified
        return loss, grad.ravel()

    def run(self):
        restarts = 0
        stop_reason = "time limit"
        try:
            while time.monotonic() < self.deadline:
                logs = self.rng.normal(0, 2, self.n*self.h)
                if self.initialization == "paired":
                    rows = logs.reshape(self.h, self.n)
                    rows[1:2*(self.h//2):2] = (rows[:2*(self.h//2):2] +
                        self.rng.normal(0, .1, (self.h//2, self.n)))
                if not restarts and self.initial_logs is not None:
                    assert self.initial_logs.size == self.n*self.h
                    logs = self.initial_logs.copy().ravel()
                checkpoint = self.out / f"checkpoint-{self.label_kind}-n{self.n}-h{self.h}-seed{self.seed}.npz"
                if not restarts and self.resume and checkpoint.exists():
                    saved = np.load(checkpoint)
                    assert np.array_equal(saved['labels'], self.y)
                    assert np.array_equal(saved['orientation'], self.orientation)
                    logs = saved['logs'].copy()
                if restarts and self.best_errors < len(self.x)//4:
                    logs = self.best_logs + self.rng.normal(0, .5, logs.shape)
                self.previous = None
                opt.minimize(self.objective, logs, jac=True, method="L-BFGS-B",
                             bounds=[(-20, 20)]*len(logs),
                             options={"maxiter": 100000, "gtol": 1e-10, "ftol": 1e-14,
                                      "maxls": 40, "maxcor": 30})
                restarts += 1
                self.score_penalty = max(self.score_penalty*.1, 1e-11)
        except TimeLimit:
            pass
        except Certified:
            stop_reason = "integer certificate"
        return {"n": self.n, "heads": self.h, "seed": self.seed,
                "label_kind": self.label_kind, "evaluations": self.evaluations,
                "initialization": self.initialization,
                "seconds": time.monotonic()-self.start, "best_errors": self.best_errors,
                "best_loss": self.best_loss, "certificate": self.certificate,
                "restarts": restarts, "stop_reason": stop_reason,
                "failure_is_not_a_lower_bound": True, "events": self.events}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--seconds", type=float, default=3600)
    p.add_argument("--trial-seconds", type=float, default=600)
    p.add_argument("--dimensions", type=int, nargs="+", default=[10, 11, 12])
    p.add_argument("--constants", type=float, nargs="+", default=[2, 3, 4])
    p.add_argument("--seed", type=int, default=60000)
    p.add_argument("--labels", choices=["random", "parity", "bent"], default="random")
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--gradient-check", action="store_true")
    p.add_argument("--inner-method", choices=["newton", "lbfgs"], default="newton")
    p.add_argument("--score-penalty", type=float, default=1e-7)
    p.add_argument("--resume", action="store_true")
    p.add_argument("--initialization", choices=["independent", "paired"], default="independent")
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.gradient_check:
        problem = Problem(5, 3, args.seed, 120, args.out, "parity")
        problem.check_certificate = False
        logs = problem.rng.normal(0, 1, 15)
        f, g = problem.objective(logs)
        direction = problem.rng.normal(0, 1, 15)
        direction /= np.linalg.norm(direction)
        eps = 1e-4
        plus = problem.objective(logs+eps*direction)[0]
        minus = problem.objective(logs-eps*direction)[0]
        print(json.dumps({"loss": f, "analytic": float(g @ direction),
                          "finite_difference": (plus-minus)/(2*eps)}))
        return
    start, trial = time.monotonic(), 0
    while time.monotonic()-start < args.seconds:
        n = args.dimensions[trial % len(args.dimensions)]
        c = args.constants[(trial//len(args.dimensions)) % len(args.constants)]
        h = max(n, math.ceil(c*(1 << n)/n**2))
        problem = Problem(n, h, args.seed+trial,
                          min(args.trial_seconds, args.seconds-(time.monotonic()-start)),
                          args.out, args.labels, args.inner_method, args.score_penalty, args.resume,
                          args.initialization)
        result = problem.run()
        with (args.out/"trials.jsonl").open("a") as stream:
            stream.write(json.dumps(result)+"\n")
        print(json.dumps({k:v for k,v in result.items() if k != "events"}), flush=True)
        trial += 1


if __name__ == "__main__":
    main()
