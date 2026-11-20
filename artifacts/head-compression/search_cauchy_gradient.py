#!/usr/bin/env python3
"""Adaptive positive Cauchy poles with high-precision LP envelope gradients.

The finite promised grid is the only scope of this experiment. Exact rational
sign checks are mandatory for successes. Run through heavy.
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
from flint import arb, arb_mat
from search_cauchy_arb import grid_basis
from refit_high_precision import exact_midpoint, rational_ball, select_hinge_basis
from verify_cauchy_grid import verify


def fit(logs, sigma, labels, bits):
    m,k = labels.shape
    h = len(logs)
    b = [Fraction(float(v)) for v in np.exp(logs)]
    f, inverse, q, r, bb = grid_basis(b,sigma,m,bits)
    y = labels.ravel()
    matrix = sp.hstack((-sp.csr_matrix(y[:,None]*q),-sp.eye(m*k)),format="csr")
    lp = opt.linprog(np.r_[np.zeros(h),np.ones(m*k)],A_ub=matrix,
        b_ub=-np.ones(m*k),bounds=[(None,None)]*h+[(0,None)]*(m*k),method="highs",
        options={"time_limit":30,"dual_feasibility_tolerance":1e-9,
                 "primal_feasibility_tolerance":1e-9})
    if not lp.success:
        raise ArithmeticError(lp.message)
    margins = y*(q@lp.x[:h])
    if margins.min()>1e-6:
        z=la.solve_triangular(r,lp.x[:h],check_finite=False)
        coefficients=inverse*arb_mat([[rational_ball(v)] for v in z])
        return 0.,np.zeros(h),coefficients,b,margins
    multipliers=-lp.ineqlin.marginals
    fractional=select_hinge_basis(q,margins,multipliers)
    selected=set(fractional.tolist())
    active=np.array([int(i) for i in np.flatnonzero(multipliers>=1-1e-7)
                     if i not in selected],dtype=int)
    fk=arb_mat([[f[i,j] for j in range(h)] for i in fractional])
    coefficients=fk.solve(arb_mat([[int(y[i])] for i in fractional]))
    rhs=arb_mat([[sum((f[i,j]*int(y[i]) for i in active),arb(0))] for j in range(h)])
    wk=fk.transpose().solve(rhs)
    w=[arb(0) for _ in range(m*k)]
    for i in active:
        w[i]=arb(-int(y[i]))
    for j,i in enumerate(fractional):
        w[i]=wk[j,0]
        multiplier=float((-int(y[i])*w[i]).mid())
        if not -1e-7<=multiplier<=1+1e-7:
            raise ArithmeticError("dual refit outside its allowed interval")
    scores=f*coefficients
    actual=np.array([int(y[i])*float(scores[i,0].mid()) for i in range(m*k)])
    active_set=set(active.tolist())
    fractional_set=set(fractional.tolist())
    if (np.max(np.abs(actual[fractional]-1))>1e-7 or
        any(actual[i]>1+1e-7 for i in active) or
        any(actual[i]<1-1e-7 for i in range(m*k)
            if i not in active_set and i not in fractional_set)):
        raise ArithmeticError("primal refit has an inconsistent hinge active set")
    gradient=[]
    for t in range(h):
        value=sum((w[i]*coefficients[t,0]*f[i,t]*
            ((i//k+1)-bb[t])/((i//k+1)+bb[t]) for i in range(m*k)),arb(0))
        gradient.append(float(value.mid())/(m*k))
    return float(np.maximum(1-actual,0).mean()),np.array(gradient),coefficients,b,actual


class StopSearch(Exception):
    pass


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--seconds",type=float,default=21600)
    parser.add_argument("--bits",type=int,default=768)
    parser.add_argument("--k",type=int,default=4)
    parser.add_argument("--seed",type=int,default=230002)
    parser.add_argument("--checkpoint",type=Path)
    args=parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    m,k=1<<args.k,args.k
    rng=np.random.default_rng(args.seed)
    codebook=2*((np.arange(m)[:,None]>>np.arange(k))&1)-1
    sigma=np.tile(codebook,(2,1))
    labels=codebook[rng.permutation(m)]
    start=time.monotonic()
    evaluations,best,restarts=0,float("inf"),0
    def objective(logs):
        nonlocal evaluations,best
        if time.monotonic()-start>=args.seconds:
            raise StopSearch
        loss,gradient,coefficients,b,margins=fit(logs,sigma,labels,args.bits)
        evaluations+=1
        if loss<best:
            best=loss
            np.savez(args.out/"checkpoint.npz",logs=logs,labels=labels,sigma=sigma)
            print(json.dumps({"evaluation":evaluations,"seconds":time.monotonic()-start,
                "loss":loss,"errors":int((margins<=0).sum()),
                "gradient_norm":float(la.norm(gradient)),"restart":restarts}),flush=True)
        if margins.min()>1e-6:
            a=[exact_midpoint(coefficients[t,0]) for t in range(len(b))]
            exact=[int(labels[p-1,j])*sum((4*a[t]*b[t]*int(sigma[t,j])/(p+b[t])**2
                for t in range(len(b))),Fraction(0)) for p in range(1,m+1) for j in range(k)]
            if min(exact)<=0:
                raise ArithmeticError("exact sign audit failed")
            margin=min(exact)
            candidate=args.out/"certificate.json"
            candidate.write_text(json.dumps({"a":[[v.numerator,v.denominator] for v in a],
                "b":[[v.numerator,v.denominator] for v in b],"labels":labels.tolist(),
                "sigma":sigma.tolist(),"margin":[margin.numerator,margin.denominator],
                "scope":"Exact promised-grid signs only."})+"\n")
            print(json.dumps(verify(candidate)),flush=True)
            raise StopSearch
        return loss,gradient
    while time.monotonic()-start<args.seconds:
        if restarts==0 and args.checkpoint is not None:
            saved=np.load(args.checkpoint)
            assert np.array_equal(saved["labels"],labels)
            assert np.array_equal(saved["sigma"],sigma)
            initial=saved["logs"]
        else:
            initial=rng.uniform(-4,np.log(m)+4,2*m)
        try:
            opt.minimize(objective,initial,jac=True,method="L-BFGS-B",
                bounds=[(-8,np.log(m)+8)]*(2*m),
                options={"maxiter":1000,"maxls":30,"ftol":1e-12,"gtol":1e-9})
        except ArithmeticError as exc:
            print(json.dumps({"restart":restarts,"rejected":str(exc)}),flush=True)
        except StopSearch:
            break
        restarts+=1
    print(json.dumps({"elapsed":time.monotonic()-start,"best_loss":best,
        "evaluations":evaluations,"restarts":restarts,"target_proved":False}),flush=True)


if __name__=="__main__":
    main()
