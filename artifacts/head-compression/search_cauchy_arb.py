#!/usr/bin/env python3
"""Search promised-grid Cauchy signs using high-precision linear bases.

This is a finite experiment, not a universal construction. All accepted
signs are checked with exact Fraction arithmetic. Run through heavy with
python-flint on PYTHONPATH.
"""
import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import time
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
import scipy.sparse as sp
from flint import arb, arb_mat, ctx, fmpq
from refit_high_precision import exact_midpoint, rational_ball


def grid_basis(b, sigma, m, bits):
    ctx.prec = bits
    k = sigma.shape[1]
    h = len(b)
    bb = [arb(fmpq(v.numerator, v.denominator)) for v in b]
    f = arb_mat([[4*bb[t]*int(sigma[t,j])/(p+bb[t])**2
                  for t in range(h)] for p in range(1,m+1) for j in range(k)])
    gram = f.transpose()*f
    lower = [[arb(0) for _ in range(h)] for _ in range(h)]
    for i in range(h):
        for j in range(i+1):
            v = gram[i,j]-sum((lower[i][t]*lower[j][t] for t in range(j)),arb(0))
            if i == j:
                if not v > 0:
                    raise ArithmeticError(f"uncertified pivot {i}")
                lower[i][j] = v.sqrt()
            else:
                lower[i][j] = v/lower[j][j]
    inverse = arb_mat(lower).transpose().inv()
    orthogonal = f*inverse
    q = np.array([[float(orthogonal[i,j].mid()) for j in range(h)]
                  for i in range(m*k)])
    qq, rr = la.qr(q, mode="economic", check_finite=False)
    return f, inverse, qq, rr, bb


def trial(b, sigma, labels, bits):
    m, k = labels.shape
    h = len(b)
    f, inverse, qq, rr, bb = grid_basis(b,sigma,m,bits)
    yy = labels.ravel()
    matrix = sp.hstack((-sp.csr_matrix(yy[:,None]*qq),-sp.eye(m*k)),format="csr")
    fit = opt.linprog(np.r_[np.zeros(h),np.ones(m*k)],A_ub=matrix,
                     b_ub=-np.ones(m*k),bounds=[(None,None)]*h+[(0,None)]*(m*k),
                     method="highs",options={"time_limit":30})
    if not fit.success:
        raise ArithmeticError(fit.message)
    margins = yy*(qq@fit.x[:h])
    record = {"loss":float(fit.fun),"errors":int((margins<=0).sum()),
              "margin":float(margins.min())}
    if margins.min() <= 1e-6:
        return record, None
    z = la.solve_triangular(rr,fit.x[:h],check_finite=False)
    coeff = inverse*arb_mat([[rational_ball(v)] for v in z])
    a = [exact_midpoint(coeff[i,0]) for i in range(h)]
    exact_margins = [int(labels[p-1,j])*sum(
        (4*a[t]*b[t]*int(sigma[t,j])/(p+b[t])**2 for t in range(h)),Fraction(0))
        for p in range(1,m+1) for j in range(k)]
    if min(exact_margins) <= 0:
        raise ArithmeticError("exact sign check rejected the floating LP output")
    margin = min(exact_margins)
    certificate = {"a":[[v.numerator,v.denominator] for v in a],
        "b":[[v.numerator,v.denominator] for v in b],
        "labels":labels.astype(int).tolist(),"sigma":sigma.astype(int).tolist(),
        "margin":[margin.numerator,margin.denominator],
        "scope":"Exact promised-grid kernel signs only; no full-cube upper bound."}
    return record, certificate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--seconds",type=float,default=21600)
    parser.add_argument("--trial-seconds",type=float,default=600)
    parser.add_argument("--bits",type=int,default=768)
    args = parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    start, case = time.monotonic(), 0
    while time.monotonic()-start < args.seconds:
        k = (2,3,4,5)[case%4]
        m = 1 << k
        seed = 230000+case
        rng = np.random.default_rng(seed)
        codebook = 2*((np.arange(m)[:,None]>>np.arange(k))&1)-1
        sigma = np.tile(codebook,(2,1))
        kind = "permutation" if case%8<4 else "random"
        labels = codebook[rng.permutation(m)] if kind=="permutation" else rng.choice([-1,1],(m,k))
        case_start, samples, best = time.monotonic(), 0, float("inf")
        certificate = None
        while (time.monotonic()-case_start < args.trial_seconds and
               time.monotonic()-start < args.seconds):
            samples += 1
            # Rational poles avoid importing floating uncertainty into the
            # final certificate. Their random ordering changes the code-to-pole assignment.
            b = [Fraction(float(v)) for v in np.exp(rng.uniform(-4,np.log(m)+4,2*m))]
            try:
                result, certificate = trial(b,sigma,labels,args.bits)
            except ArithmeticError as exc:
                print(json.dumps({"case":case,"sample":samples,"rejected":str(exc)}),flush=True)
                continue
            if result["loss"] < best:
                best = result["loss"]
                print(json.dumps({"k":k,"seed":seed,"kind":kind,"sample":samples,
                    "seconds":time.monotonic()-case_start,**result}),flush=True)
            if certificate is not None:
                path = args.out/f"grid-k{k}-seed{seed}.json"
                path.write_text(json.dumps(certificate)+"\n")
                break
        record = {"k":k,"seed":seed,"kind":kind,"samples":samples,
            "seconds":time.monotonic()-case_start,"best_loss":best,
            "certificate":str(path) if certificate is not None else None,
            "failure_is_not_a_lower_bound":True}
        with (args.out/"results.jsonl").open("a") as stream:
            stream.write(json.dumps(record)+"\n")
        print(json.dumps(record),flush=True)
        case += 1


if __name__ == "__main__":
    main()
