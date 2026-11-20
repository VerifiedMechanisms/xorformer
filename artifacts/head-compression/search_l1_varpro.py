#!/usr/bin/env python3
"""Variable projection with LP inner optimization of hinge loss.

This changes the search objective, not the attention model. Any accepted
table is independently checked with integer arithmetic. Use heavy.
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
import scipy.sparse as sp
from search_varpro_scores import Problem, TimeLimit, Certified
from search_newton_scores import export
from search_sign_scores import exact_check


class L1Problem(Problem):
    def objective(self, logs):
        if time.monotonic() >= self.deadline:
            raise TimeLimit
        b = np.exp(logs.reshape(self.h, self.n))
        d = 1+np.einsum("xhi,hi->xh", self.t, b)
        features = np.column_stack((np.ones(len(self.x)),
                                    (self.t/d[:, :, None]).reshape(len(self.x), -1)))
        q, r = la.qr(features, mode="economic", check_finite=False)
        yq = self.y[:, None]*q
        rows, columns = yq.shape
        matrix = sp.hstack((-sp.csr_matrix(yq), -sp.eye(rows)), format="csr")
        fit = opt.linprog(np.r_[np.zeros(columns), np.ones(rows)],
                          A_ub=matrix, b_ub=-np.ones(rows),
                          bounds=[(None, None)]*columns+[(0, None)]*rows,
                          method="highs",
                          options={"dual_feasibility_tolerance": 1e-8,
                                   "primal_feasibility_tolerance": 1e-8})
        if not fit.success:
            raise RuntimeError(f"Inner LP failed: {fit.message}")
        coeff = la.solve_triangular(r, fit.x[:columns], check_finite=False)
        score = q @ fit.x[:columns]
        margin = self.y*score
        loss = float(fit.fun/rows)
        u = coeff[1:].reshape(self.h, self.n)
        num = np.einsum("xhi,hi->xh", self.t, u)
        # SciPy's inequality marginals are minus the nonnegative KKT
        # multipliers for A*z <= b. Differentiate in the original
        # numerator coordinates, whose attainable span is unchanged by QR.
        weights = -fit.ineqlin.marginals*self.y
        grad = np.einsum("x,xh,xhi,hi->hi", weights, num/d**2, self.t, b)/rows
        self.evaluations += 1
        errors = int((margin <= 0).sum())
        self.best_errors = min(self.best_errors, errors)
        if loss < self.best_loss:
            self.best_loss = loss
            self.best_logs, self.best_coeff = logs.copy(), coeff.copy()
            np.savez(self.out/"checkpoint.npz", logs=logs, coefficients=coeff,
                     orientation=self.orientation, labels=self.y)
        event = {"evaluation": self.evaluations, "seconds": time.monotonic()-self.start,
                 "loss": loss, "errors": errors, "min_margin": float(margin.min()),
                 "coefficient_max": float(np.max(np.abs(coeff))),
                 "score_discrepancy": float(np.max(np.abs(features @ coeff-score))),
                 "kink_count": int((np.abs(margin-1) < 1e-6).sum())}
        self.events.append(event)
        if time.monotonic()-self.last_log >= 30:
            print(json.dumps({"progress": True, "n": self.n, "heads": self.h,
                              **event}), flush=True)
            self.last_log = time.monotonic()
        if self.check_certificate and margin.min() > 1e-6:
            cert = export(self.n, self.y, u, b, self.orientation, coeff[0])
            check = exact_check(cert)
            if check["certified"]:
                self.certified_logs, self.certified_coeff = logs.copy(), coeff.copy()
                cert["verification"] = check
                self.certificate = "certificate.json"
                (self.out/self.certificate).write_text(json.dumps(cert)+"\n")
                raise Certified
        return loss, grad.ravel()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=28800)
    parser.add_argument("--seed", type=int, default=180000)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    saved = np.load(args.checkpoint)
    labels = saved["labels"].copy()
    n, h = int(math.log2(len(labels))), len(saved["orientation"])
    problem = L1Problem(n, h, args.seed, args.seconds, args.out, "l1", score_penalty=0)
    problem.y, problem.orientation = labels, saved["orientation"].copy()
    problem.t = np.where(problem.orientation[None, :, None] > 0,
                         problem.x[:, None, :], 1-problem.x[:, None, :])
    problem.initial_logs = saved["logs"].copy()
    result = problem.run()
    result["objective"] = "ordinary hinge loss with LP numerator optimization"
    (args.out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "events"}), flush=True)


if __name__ == "__main__":
    main()
