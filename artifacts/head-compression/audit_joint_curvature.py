#!/usr/bin/env python3
"""Audit joint curvature at a finite checkpoint, with all heads coupled.

Unlike block curvature, this includes cancellation between the first variations
of different heads. Eigenvalues and descent tests are numerical diagnostics,
not certificates of a local optimum or a universal theorem. Run with heavy.
"""
import argparse
import json
import os
from pathlib import Path
import time

for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
from scipy.sparse.linalg import LinearOperator, eigsh, lobpcg, ArpackNoConvergence
from search_block_curvature import head_data, derivatives


def run(checkpoint, out, seconds, solver):
    start = time.monotonic()
    deadline = start+seconds
    saved = np.load(checkpoint)
    y = saved["labels"].astype(float)
    orientation = saved["orientation"].astype(int)
    logs = saved["logs"].copy()
    h, n = logs.shape
    coefficient = saved["coefficients"]
    np.savez(out/"input-checkpoint.npz", labels=y, orientation=orientation,
             logs=logs, coefficients=coefficient)
    values = coefficient[1:].reshape(h, n)/np.exp(logs)
    bias = float(coefficient[0])
    x = ((np.arange(len(y))[:, None] >> np.arange(n)) & 1).astype(float)
    t_for = lambda j: x if orientation[j] > 0 else 1-x
    score = bias+sum(head_data(t_for(j), logs[j], values[j])[0] for j in range(h))
    r = np.maximum(1-y*score, 0)
    active = r > 0
    weight = y*r
    loss = float(r@r/(2*len(y)))
    dimension = 1+2*n*h
    jac = np.empty((len(y), dimension))
    jac[:, 0] = 1
    normalizers = np.empty(dimension)
    normalizers[0] = 1/np.sqrt(active.mean())
    jac[:, 0] *= normalizers[0]
    curvature = np.empty((h, 2*n, 2*n))
    value_scales = np.empty(h)
    for j in range(h):
        q, p = head_data(t_for(j), logs[j], values[j])
        scale = max(1., float(np.max(np.abs(values[j]))))
        value_scales[j] = scale
        local_jac = np.column_stack((scale*p, p*(values[j]-q[:, None])))
        _, local_hessian = derivatives(p, values[j], score, y, scale)
        local_curvature = local_jac[active].T@local_jac[active]/len(y)-local_hessian
        norm = np.sqrt(np.sum(local_jac[active]**2, axis=0)/len(y))
        inverse = 1/np.maximum(norm, 1e-14)
        sl = slice(1+2*n*j, 1+2*n*(j+1))
        normalizers[sl] = inverse
        jac[:, sl] = local_jac*inverse
        curvature[j] = local_curvature*inverse[:, None]*inverse[None, :]
    gradient = -jac.T@weight/len(y)
    calls = 0
    def multiply(v):
        nonlocal calls
        v = np.asarray(v).reshape(-1)
        if time.monotonic() > deadline:
            raise TimeoutError("Joint curvature audit reached its time limit")
        calls += 1
        z = jac@v
        z[~active] = 0
        ans = jac.T@z/len(y)
        ans[1:] -= np.einsum("hij,hj->hi", curvature,
                             v[1:].reshape(h, 2*n)).ravel()
        if calls % 25 == 0:
            print(json.dumps({"matvecs": calls, "seconds": time.monotonic()-start}),
                  flush=True)
        return ans
    operator = LinearOperator((dimension, dimension), matvec=multiply,
                              rmatvec=multiply, dtype=float)
    result = {"n": n, "heads": h, "loss": loss,
              "errors": int((y*score <= 0).sum()),
              "minimum_distance_to_hinge_kink": float(np.min(np.abs(1-y*score))),
              "normalized_gradient_norm": float(np.linalg.norm(gradient)),
              "scope": "Numerical diagnostic only; no local or global optimality certificate."}
    try:
        if solver == "lobpcg":
            initial = np.random.default_rng(460003).normal(size=(dimension, 3))
            eigenvalues, eigenvectors, history = lobpcg(
                operator, initial, largest=False, tol=1e-7, maxiter=1000,
                retResidualNormsHistory=True)
            result["eigensolver"] = "finite-iteration LOBPCG approximation"
            result["last_residual_norms"] = np.asarray(history[-1]).tolist()
        else:
            eigenvalues, eigenvectors = eigsh(operator, k=3, which="SA", tol=1e-5,
                                              maxiter=300, ncv=40)
            result["eigensolver"] = "converged"
    except ArpackNoConvergence as error:
        eigenvalues, eigenvectors = error.eigenvalues, error.eigenvectors
        result["eigensolver"] = "partial convergence"
    except TimeoutError:
        eigenvalues = np.array([])
        eigenvectors = np.empty((dimension, 0))
        result["eigensolver"] = "time limit"
    result["eigenvalues"] = eigenvalues.tolist()
    trials = []
    best = None
    if len(eigenvalues):
        np.savez(out/"eigenvectors.npz", eigenvalues=eigenvalues,
                 eigenvectors=eigenvectors, normalizers=normalizers,
                 value_scales=value_scales)
        for k in range(len(eigenvalues)):
            if eigenvalues[k] >= 0:
                continue
            direction = normalizers*eigenvectors[:, k]
            direction /= max(np.max(np.abs(direction[1:])), 1e-30)
            blocks = direction[1:].reshape(h, 2*n)
            for sign in (-1, 1):
                for magnitude in (1e-3, .01, .1, .5, 1.):
                    alpha = sign*magnitude
                    trial_values = values+alpha*value_scales[:, None]*blocks[:, :n]
                    trial_logs = np.clip(logs+alpha*blocks[:, n:], -35, 35)
                    trial_bias = bias+alpha*direction[0]
                    trial_score = trial_bias+sum(
                        head_data(t_for(j), trial_logs[j], trial_values[j])[0]
                        for j in range(h))
                    trial_r = np.maximum(1-y*trial_score, 0)
                    trial_loss = float(trial_r@trial_r/(2*len(y)))
                    trial = {"eigenvector": k, "alpha": alpha, "loss": trial_loss,
                             "errors": int((y*trial_score <= 0).sum())}
                    trials.append(trial)
                    if trial_loss < loss and (best is None or trial_loss < best[0]):
                        best = (trial_loss, trial_values, trial_logs, trial_bias)
        if best is not None:
            new_loss, new_values, new_logs, new_bias = best
            np.savez(out/"descent-checkpoint.npz", labels=y, orientation=orientation,
                     logs=new_logs,
                     coefficients=np.r_[new_bias,(new_values*np.exp(new_logs)).ravel()])
            result["best_trial_loss"] = new_loss
    result["trials"] = trials
    result["matvecs"] = calls
    result["seconds"] = time.monotonic()-start
    (out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--solver", choices=["arpack", "lobpcg"], default="lobpcg")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.checkpoint, args.out, args.seconds, args.solver)
