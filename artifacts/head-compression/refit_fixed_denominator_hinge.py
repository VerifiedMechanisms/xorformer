#!/usr/bin/env python3
"""Refit a saved score with fixed denominators and no score penalty.

Optimization is only a search heuristic. A reported certificate must pass
integer/Fraction evaluation on the full cube. Run through heavy.
"""
import argparse
import json
import os
from pathlib import Path
import time

for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
from search_newton_scores import export
from search_sign_scores import exact_check


class StopSearch(Exception):
    pass


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=1800)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    saved = np.load(args.checkpoint)
    labels = saved["labels"].copy()
    orientation = saved["orientation"].copy()
    previous = saved["coefficients"].copy()
    logs = saved["logs"].copy()
    n, h = (len(labels).bit_length() - 1), len(orientation)
    assert len(labels) == 1 << n and logs.size == n * h
    assert previous.shape == (1 + n * h,)
    assert np.all(np.isin(labels, [-1, 1]))
    assert np.all(np.isin(orientation, [-1, 1]))
    start = time.monotonic()
    deadline = start + args.seconds
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    t = np.where(orientation[None, :, None] > 0, x[:, None, :], 1 - x[:, None, :])
    b = np.exp(logs.reshape(h, n))
    denominators = 1 + np.einsum("xhi,hi->xh", t, b)
    features = np.column_stack((np.ones(len(x)),
                               (t / denominators[:, :, None]).reshape(len(x), -1)))
    q, r = la.qr(features, mode="economic", check_finite=False)
    initial = q.T @ (features @ previous)
    yq = labels[:, None] * q
    last_report = start
    evaluations = 0
    best_errors = len(x)
    certificate_path = None
    attempted_threshold = 1e-4

    def objective(z):
        nonlocal evaluations, last_report, best_errors, certificate_path, attempted_threshold
        if time.monotonic() >= deadline:
            raise StopSearch
        margin = yq @ z
        residual = np.maximum(1 - margin, 0)
        value = .5 * residual @ residual
        gradient = -(yq.T @ residual)
        evaluations += 1
        errors = int(np.count_nonzero(margin <= 0))
        best_errors = min(best_errors, errors)
        if time.monotonic() - last_report > 30:
            print(json.dumps({"n": n, "heads": h, "evaluations": evaluations,
                              "seconds": time.monotonic() - start,
                              "loss": float(value) / len(x), "errors": errors,
                              "min_margin": float(np.min(margin)),
                              "gradient": float(np.max(np.abs(gradient)))}), flush=True)
            last_report = time.monotonic()
        if float(np.min(margin)) > attempted_threshold:
            coefficients = la.solve_triangular(r, z, check_finite=False)
            cert = export(n, labels, coefficients[1:].reshape(h, n), b,
                          orientation, coefficients[0])
            check = exact_check(cert)
            if check["certified"]:
                cert["verification"] = check
                certificate_path = str(args.out / "certificate.json")
                Path(certificate_path).write_text(json.dumps(cert) + "\n")
                raise StopSearch
            print(json.dumps({"exact_export_failed": check,
                              "floating_margin": float(np.min(margin))}), flush=True)
            attempted_threshold *= 10
        return value, gradient

    try:
        opt.minimize(objective, initial, jac=True, method="L-BFGS-B",
                     options={"maxiter": 100000, "gtol": 1e-10, "ftol": 1e-16,
                              "maxls": 50, "maxcor": 100})
    except StopSearch:
        pass
    result = {"n": n, "heads": h, "seconds": time.monotonic() - start,
              "evaluations": evaluations, "best_errors": best_errors,
              "certificate": certificate_path,
              "scope": "This fixed denominator list and truth table only.",
              "failure_is_not_a_lower_bound": True}
    (args.out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
