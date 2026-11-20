#!/usr/bin/env python3
"""Test a binary-address Cauchy memory mechanism on finite promised grids.

The searched matrix has entries sum_h a_h sigma[h,j] 4*p*b_h/(p+b_h)^2.
Only exact Fraction checks of the unscaled matrix are reported as successes.
This mechanism has no established arbitrary-table or full-cube theorem.
Run through heavy.
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
import scipy.optimize as opt


def exact_grid(a, b, labels, sigma):
    aa = [Fraction(float(v)) for v in a]
    bb = [Fraction(float(v)) for v in b]
    minimum = None
    for p in range(1, len(labels)+1):
        for j in range(labels.shape[1]):
            score = sum((4*aa[h]*bb[h]*int(sigma[h,j])/(p+bb[h])**2
                         for h in range(len(a))), Fraction(0))
            margin = int(labels[p-1,j])*score
            if margin <= 0:
                return None
            minimum = margin if minimum is None else min(minimum, margin)
    return {"a": [[v.numerator,v.denominator] for v in aa],
            "b": [[v.numerator,v.denominator] for v in bb],
            "labels": labels.astype(int).tolist(),
            "sigma": sigma.astype(int).tolist(),
            "margin": [minimum.numerator,minimum.denominator],
            "scope": "Exact promised-grid kernel signs only; no full-cube upper bound."}


def run_case(k, seed, seconds, out, kind, copies=1):
    m = 1 << k
    h = copies*m
    rng = np.random.default_rng(seed)
    codebook = 2*((np.arange(m)[:,None] >> np.arange(k)) & 1)-1
    sigma = np.tile(codebook,(copies,1))
    if kind == "permutation":
        labels = codebook[rng.permutation(m)]
    else:
        labels = rng.choice([-1,1], size=(m,k))
    p = np.arange(1,m+1)[:,None]
    start, best, trials = time.monotonic(), float("inf"), 0
    best_errors = m*k
    def values(parameters, jacobian=False):
        a, b = parameters[:h], np.exp(parameters[h:])
        kernel = 4*p*b[None,:]/(p+b[None,:])**2
        score = (kernel*a[None,:]) @ sigma
        residual = np.maximum(1-labels*score, 0)
        if not jacobian:
            return residual.ravel()
        derivative = kernel*(p-b[None,:])/(p+b[None,:])
        ja = kernel[:,None,:]*sigma.T[None,:,:]
        jb = (derivative*a[None,:])[:,None,:]*sigma.T[None,:,:]
        return (-(labels*(residual > 0))[:,:,None]*np.concatenate((ja,jb),axis=2)).reshape(m*k,2*h)
    while time.monotonic()-start < seconds:
        initial = np.r_[rng.normal(0,10,h), rng.normal(np.log(m/2),3,h)]
        initial[h:] = np.clip(initial[h:],-25,25)
        result = opt.least_squares(values, initial, jac=lambda v:values(v, True),
                                   bounds=(np.r_[np.full(h,-np.inf),np.full(h,-30)],
                                           np.r_[np.full(h,np.inf),np.full(h,30)]),
                                   max_nfev=1000, ftol=1e-10, xtol=1e-10, gtol=1e-10)
        trials += 1
        a, b = result.x[:h], np.exp(result.x[h:])
        score = ((4*p*b[None,:]/(p+b[None,:])**2)*a[None,:]) @ sigma
        margins = labels*score
        loss = float(np.maximum(1-margins,0).mean())
        best_errors = min(best_errors,int((margins <= 0).sum()))
        if loss < best:
            best = loss
            np.savez(out/f"best-k{k}-seed{seed}.npz",a=a,b=b,labels=labels,sigma=sigma)
            print(json.dumps({"k":k,"m":m,"poles":h,"copies":copies,"kind":kind,"seed":seed,"trial":trials,
                              "seconds":time.monotonic()-start,"loss":loss,
                              "errors":int((margins <= 0).sum())}),flush=True)
        if margins.min() > 1e-6:
            certificate = exact_grid(a,b,labels,sigma)
            if certificate is not None:
                path = out/f"grid-k{k}-seed{seed}.json"
                path.write_text(json.dumps(certificate)+"\n")
                return {"k":k,"poles":h,"copies":copies,"seed":seed,"kind":kind,"certificate":str(path),
                        "trials":trials,"seconds":time.monotonic()-start}
    return {"k":k,"poles":h,"copies":copies,"seed":seed,"kind":kind,"certificate":None,"trials":trials,
            "best_loss":best,"best_errors":best_errors,"seconds":time.monotonic()-start,
            "failure_is_not_a_lower_bound":True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--seconds",type=float,default=25200)
    parser.add_argument("--trial-seconds",type=float,default=900)
    parser.add_argument("--copies",type=int,default=1)
    args = parser.parse_args()
    if args.copies < 1:
        parser.error("--copies must be positive")
    args.out.mkdir(parents=True,exist_ok=True)
    deadline, trial = time.monotonic()+args.seconds, 0
    while time.monotonic() < deadline:
        k = (2,3,4,5)[trial % 4]
        kind = "permutation" if trial % 8 < 4 else "random"
        record = run_case(k,220000+trial,min(args.trial_seconds,deadline-time.monotonic()),args.out,kind,args.copies)
        with (args.out/"results.jsonl").open("a") as stream:
            stream.write(json.dumps(record)+"\n")
        print(json.dumps(record),flush=True)
        trial += 1


if __name__ == "__main__":
    main()
