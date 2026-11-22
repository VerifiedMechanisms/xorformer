#!/usr/bin/env python3
"""Replace two heads by one using fixed-residual linear feasibility.

Numerical proposals only. Every successful full score is exported with
rational coefficients and independently checked. Failure proves neither
local infeasibility nor any universal lower bound. Run with heavy.
"""
import argparse
from fractions import Fraction
import json
import math
import os
from pathlib import Path
import sys
import time
for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
from scipy.optimize import linprog
from audit_rational_score import audit
from audit_pair_merges import integer_head
sys.set_int_max_str_digits(0)


def values(data):
    n = data["n"]
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(np.longdouble)
    xa = np.column_stack((np.ones(len(x), dtype=np.longdouble), x))
    pieces = []
    for h in data["heads"]:
        b = np.array([np.longdouble(str(v)) for v in h["denominator"]])
        a = np.array([np.longdouble(str(v)) for v in h["numerator"]])
        pieces.append((xa@a)/(xa@b))
    pieces = np.array(pieces).T
    bias = np.longdouble(str(data["bias"][0]))/np.longdouble(str(data["bias"][1]))
    return x, pieces, bias+pieces.sum(axis=1)


def proposed_head(u, beta, scale, orientation):
    a = [Fraction(float(scale))*Fraction(float(v)) for v in u]
    b = [Fraction(float(v)) for v in beta]
    if orientation < 0:
        a = [sum(a)]+[-v for v in a[1:]]
        b = [sum(b)]+[-v for v in b[1:]]
    return integer_head(a, b)


def run(source, out, seconds, max_pairs, seed, lp_seconds):
    data = json.loads(source.read_text())
    x, pieces, score = values(data)
    labels = np.array(data["labels"])
    assert np.min(labels*score) > 0
    heads, n = pieces.shape[1], data["n"]
    rng = np.random.default_rng(seed)
    chosen = rng.choice(len(x), min(len(x), 512), replace=False)
    sample = np.asarray(pieces[chosen], dtype=float)
    sample -= sample.mean(axis=0)
    norm = np.linalg.norm(sample, axis=0)
    sample /= np.maximum(norm, 1e-100)
    gram = sample.T@sample
    pairs = [(i,j) for i in range(heads) for j in range(i+1,heads)]
    pairs.sort(key=lambda pair: -abs(gram[pair]))
    # Correlation is a proposal ranking, not a merging certificate.
    pairs = pairs[:max_pairs]
    xa = np.column_stack((np.ones(len(x)), np.asarray(x,dtype=float)))
    started = time.monotonic()
    events, certificate = [], None
    for order,(i,j) in enumerate(pairs):
        if time.monotonic()-started >= seconds or (out/"STOP").exists():
            break
        residual = score-pieces[:,i]-pieces[:,j]
        scale = float(max(1, np.max(np.abs(residual))))
        rr = np.asarray(residual/scale, dtype=float)
        for orientation in (1,-1):
            t = xa.copy()
            if orientation < 0:
                t[:,1:] = 1-t[:,1:]
            matrix = np.column_stack((-labels[:,None]*t,
                                       -(labels*rr)[:,None]*t,
                                       np.ones(len(x))))
            eq = np.r_[np.zeros(n+1),np.ones(n+1),0.][None]
            for floor in (1e-6,1e-10):
                remaining = seconds-(time.monotonic()-started)
                if remaining <= 0:
                    break
                objective = np.r_[np.zeros(2*(n+1)),-1.]
                fit = linprog(objective,A_ub=matrix,b_ub=np.zeros(len(x)),
                    A_eq=eq,b_eq=[1.],bounds=[(-4,4)]*(n+1)+[(floor,1)]*(n+1)+[(None,None)],
                    method="highs",options={"time_limit":min(lp_seconds,remaining),
                        "primal_feasibility_tolerance":1e-10,
                        "dual_feasibility_tolerance":1e-10})
                event = {"pair":[i,j],"order":order,"orientation":orientation,
                    "floor":floor,"seconds":time.monotonic()-started,
                    "status":int(fit.status),"message":fit.message,"scale":scale}
                if fit.x is not None:
                    u,beta = fit.x[:n+1],fit.x[n+1:2*(n+1)]
                    event["cleared_slack"] = float(fit.x[-1])
                    if np.min(beta) > 0:
                        candidate = residual+np.longdouble(scale)*(t.astype(np.longdouble)@u.astype(np.longdouble))/(t.astype(np.longdouble)@beta.astype(np.longdouble))
                        margin = labels*candidate
                        event.update(errors=int((margin<=0).sum()),minimum_margin=float(margin.min()))
                        if margin.min() > 1e-5:
                            new = {"n":n,"labels":data["labels"],"bias":data["bias"],
                                "heads":[h for k,h in enumerate(data["heads"]) if k not in (i,j)]+[proposed_head(u,beta,scale,orientation)],
                                "scope":"One fixed truth table only; no universal theorem.",
                                "pair_completion":{"pair":[i,j],"orientation":orientation,"floor":floor}}
                            path=out/"candidate.json";path.write_text(json.dumps(new)+"\n")
                            checked=audit(path,224)
                            event["exact_signs_certified"]=checked["all_target_signs_certified"]
                            if checked["all_target_signs_certified"]:
                                final=out/"certificate.json";path.replace(final)
                                (out/"certificate-audit.json").write_text(json.dumps(checked,indent=2)+"\n")
                                certificate=final.name
                events.append(event)
                with (out/"events.jsonl").open("a") as stream:
                    stream.write(json.dumps(event)+"\n")
                print(json.dumps(event),flush=True)
                if certificate is not None:
                    break
            if certificate is not None:
                break
        if certificate is not None:
            break
    result={"n":n,"initial_heads":heads,"candidate_heads":heads-1,
        "seconds":time.monotonic()-started,"lp_calls":len(events),"certificate":certificate,
        "scope":"Fixed residual pair completion, numerical proposals followed by exact audit.",
        "failure_is_not_a_lower_bound":True}
    (out/"result.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result),flush=True)


if __name__ == "__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("certificate",type=Path)
    p.add_argument("--out",type=Path,required=True)
    p.add_argument("--seconds",type=float,default=14400)
    p.add_argument("--pairs",type=int,default=50000)
    p.add_argument("--seed",type=int,default=2026112219)
    p.add_argument("--lp-seconds",type=float,default=30)
    args=p.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    run(args.certificate,args.out,args.seconds,args.pairs,args.seed,args.lp_seconds)
