#!/usr/bin/env python3
"""Search exact affine multiset switching identities on the Boolean cube.

Two lists agree as multisets off one vertex and differ at that vertex.
SAT certificates are checked with exact rational arithmetic. Timeout is not
an impossibility result. This auxiliary construction does not prove W(n).
Run through heavy.
"""
import argparse
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
import time
import z3


def run(n,h,seconds,out):
    solver=z3.Solver()
    solver.set(timeout=int(seconds*1000))
    left=[[z3.RealVal(0)]*(n+1)]+[[z3.Real(f"c_{a}_{i}") for i in range(n+1)] for a in range(1,h)]
    right=[[z3.Real(f"d_{a}_{i}") for i in range(n+1)] for a in range(h)]
    def value(row,x):
        return row[0]+z3.Sum([row[i+1] for i in range(n) if x>>i&1])
    # Relabel the right list to use the identity matching at the zero vertex.
    solver.add(*(left[a][0]==right[a][0] for a in range(h)))
    solver.add(*(left[a][0]<=left[a+1][0] for a in range(1,h-1)))
    for x in range(1,(1<<n)-1):
        permutation=[z3.Int(f"p_{x}_{a}") for a in range(h)]
        solver.add(z3.Distinct(permutation))
        for a in range(h):
            solver.add(0<=permutation[a],permutation[a]<h)
            solver.add(*(z3.Implies(permutation[a]==b,value(left[a],x)==value(right[b],x))
                         for b in range(h)))
    target=(1<<n)-1
    lc=[value(row,target) for row in left]
    rc=[value(row,target) for row in right]
    solver.add(z3.Sum([z3.If(v==0,1,0) for v in lc])>
               z3.Sum([z3.If(v==0,1,0) for v in rc]))
    # Every nonzero target difference can be uniformly rescaled to have
    # magnitude at least one. This excludes no nontrivial switching pair.
    solver.add(*(z3.Or(v==0,v<=-1,v>=1) for v in lc+rc))
    started=time.monotonic()
    answer=solver.check()
    record={"n":n,"terms_per_list":h,"seconds":time.monotonic()-started,
            "answer":str(answer),"scope":"Affine multiset switching only; no universal head bound."}
    if answer==z3.unknown:
        record["reason"]=solver.reason_unknown()
    elif answer==z3.sat:
        model=solver.model()
        def rational(v):
            q=model.eval(v,model_completion=True)
            return Fraction(q.numerator_as_long(),q.denominator_as_long())
        ll=[[rational(v) for v in row] for row in left]
        rr=[[rational(v) for v in row] for row in right]
        def evaluate(row,x):
            return row[0]+sum((row[i+1] for i in range(n) if x>>i&1),Fraction(0))
        for x in range(target):
            assert Counter(evaluate(row,x) for row in ll)==Counter(evaluate(row,x) for row in rr)
        assert Counter(evaluate(row,target) for row in ll)!=Counter(evaluate(row,target) for row in rr)
        base=1+max(abs(v) for row in ll+rr for v in row)
        shifted=[[v+base for v in row] for row in ll+rr]
        assert all(v>0 for row in shifted for v in row)
        path=out/f"switching-n{n}-h{h}.json"
        path.write_text(json.dumps({"n":n,"left":[[[v.numerator,v.denominator] for v in row] for row in ll],
            "right":[[[v.numerator,v.denominator] for v in row] for row in rr],
            "common_positive_base":[base.numerator,base.denominator],"exact_checked":True})+"\n")
        record["certificate"]=str(path)
    print(json.dumps(record),flush=True)
    with (out/"results.jsonl").open("a") as stream:
        stream.write(json.dumps(record)+"\n")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--seconds",type=float,default=18000)
    parser.add_argument("--trial-seconds",type=float,default=1800)
    args=parser.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    deadline=time.monotonic()+args.seconds
    cases=[(2,2),(3,3),(3,4)]+[(4,h) for h in range(4,9)]+[(5,h) for h in range(5,17)]
    for n,h in cases:
        remaining=deadline-time.monotonic()
        if remaining<=0:
            break
        run(n,h,min(args.trial_seconds,remaining),args.out)


if __name__=="__main__":
    main()
