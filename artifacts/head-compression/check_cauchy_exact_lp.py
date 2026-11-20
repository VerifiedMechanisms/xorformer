#!/usr/bin/env python3
"""Exact linear feasibility for a single prescribed Cauchy pole list.

UNSAT is only about the supplied pole list, never about adaptive poles.
Run through heavy. An accepted model is independently checked with Fraction.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time
import numpy as np
import z3
from verify_cauchy_grid import verify


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source",type=Path)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--seconds",type=float,default=600)
    args=parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    if args.source.suffix==".npz":
        data=np.load(args.source)
        b=[Fraction(float(v)) for v in np.exp(data["logs"])]
        labels=data["labels"].astype(int).tolist()
        sigma=data["sigma"].astype(int).tolist()
    else:
        data=json.loads(args.source.read_text())
        b=[Fraction(*v) for v in data["b"]]
        labels,sigma=data["labels"],data["sigma"]
    assert all(v>0 for v in b)
    m,k,h=len(labels),len(labels[0]),len(b)
    solver=z3.Solver()
    solver.set(timeout=int(1000*args.seconds))
    a=[z3.Real(f"a_{i}") for i in range(h)]
    for p in range(1,m+1):
        for j in range(k):
            coefficients=[labels[p-1][j]*4*b[t]*sigma[t][j]/(p+b[t])**2 for t in range(h)]
            terms=[z3.Q(v.numerator,v.denominator)*a[t] for t,v in enumerate(coefficients)]
            solver.add(z3.Sum(terms)>=1)
    started=time.monotonic()
    answer=solver.check()
    result={"source":str(args.source),"addresses":m,"output_bits":k,"poles":h,
            "answer":str(answer),"seconds":time.monotonic()-started,
            "scope":"This fixed positive pole list only. No adaptive-pole impossibility claim."}
    if answer==z3.unknown:
        result["reason"]=solver.reason_unknown()
    elif answer==z3.sat:
        model=solver.model()
        aa=[]
        for v in a:
            q=model.eval(v,model_completion=True)
            aa.append(Fraction(q.numerator_as_long(),q.denominator_as_long()))
        margins=[labels[p-1][j]*sum((4*aa[t]*b[t]*sigma[t][j]/(p+b[t])**2
                 for t in range(h)),Fraction(0)) for p in range(1,m+1) for j in range(k)]
        minimum=min(margins)
        assert minimum>=1
        candidate=args.out/"certificate.json"
        candidate.write_text(json.dumps({"a":[[v.numerator,v.denominator] for v in aa],
            "b":[[v.numerator,v.denominator] for v in b],"labels":labels,"sigma":sigma,
            "margin":[minimum.numerator,minimum.denominator],
            "scope":"Exact promised-grid signs only."})+"\n")
        result["verification"]=verify(candidate)
    (args.out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps(result),flush=True)


if __name__=="__main__":
    main()
