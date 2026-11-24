#!/usr/bin/env python3
"""Exact real-arithmetic satisfiability for selected small original head tasks.

A timeout/unknown is not a proof. SAT models are separately rechecked with
rational arithmetic when all values are rational. UNSAT applies only to the
explicit orientation and head-count case; the script checks each orientation.
"""
import argparse,itertools,json,time
from pathlib import Path
from datetime import datetime,timezone
import z3


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=4)
    ap.add_argument('--heads',type=int,default=2);ap.add_argument('--timeout',type=int,default=300000)
    ap.add_argument('--target',choices=['xor_and','xor_or','majority_xor','random'],default='xor_and')
    ap.add_argument('--seed',type=int,default=123);ap.add_argument('--out',type=Path,required=True)
    ar=ap.parse_args();n,H=ar.n,ar.heads
    cube=list(itertools.product([0,1],repeat=n))
    if ar.target=='xor_and':labels=[(x[0]!=x[1]) and (x[2]!=x[3]) for x in cube]
    elif ar.target=='xor_or':labels=[(x[0]!=x[1]) or (x[2]!=x[3]) for x in cube]
    elif ar.target=='majority_xor':labels=[sum(x[2*i]!=x[2*i+1] for i in range(n//2))>n//4 for x in cube]
    else:
        import random
        rr=random.Random(ar.seed);labels=[rr.choice([False,True]) for _ in cube]
    record={'started_utc':datetime.now(timezone.utc).isoformat(),'n':n,'heads':H,'target':ar.target,
            'cube_order':'lexicographic','labels':labels,'cases':[]}
    start=time.monotonic()
    for negative in range(H+1):
        orientations=[-1]*negative+[1]*(H-negative)
        a=[[z3.Real(f'a_{h}_{i}') for i in range(n+1)] for h in range(H)]
        b=[[z3.Real(f'b_{h}_{i}') for i in range(n)] for h in range(H)]
        solver=z3.SolverFor('QF_NRA');solver.set(timeout=ar.timeout)
        for row in b:
            for value in row:solver.add(value>0)
        # Absorb free bias into the first numerator. Nonconstant denominators
        # permit arbitrary affine numerators. Constant heads can be perturbed
        # into this positive-slope class for strict labels, at fixed finite H.
        for x,label in zip(cube,labels):
            D=[1+sum(b[h][i]*(x[i] if orientations[h]==1 else 1-x[i]) for i in range(n)) for h in range(H)]
            A=[a[h][0]+sum(a[h][i+1]*x[i] for i in range(n)) for h in range(H)]
            P=sum(A[h]*z3.Product([D[g] for g in range(H) if g!=h]) for h in range(H))
            solver.add(P>0 if label else P<0)
        t=time.monotonic();status=solver.check()
        case={'negative_heads':negative,'status':str(status),'seconds':time.monotonic()-t}
        if status==z3.sat:
            model=solver.model();case['a']=[[str(model.eval(v,model_completion=True)) for v in row] for row in a]
            case['b']=[[str(model.eval(v,model_completion=True)) for v in row] for row in b]
        elif status==z3.unknown:case['reason']=solver.reason_unknown()
        record['cases'].append(case);record['elapsed_seconds']=time.monotonic()-start
        ar.out.write_text(json.dumps(record,indent=2)+'\n')
        print(json.dumps(case),flush=True)
        if status==z3.sat:break
    record['finished_utc']=datetime.now(timezone.utc).isoformat()
    ar.out.write_text(json.dumps(record,indent=2)+'\n')
if __name__=='__main__':main()
