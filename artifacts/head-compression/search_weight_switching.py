#!/usr/bin/env python3
"""Exact Hamming-layer multiset switching search, not a universal head bound.

Find two affine line lists agreeing at weights 0,...,n-1 and differing at n.
All accepted output is checked with rational arithmetic. Run through heavy.
"""
import argparse
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
import time
import z3


def trial(n,h,seconds,out):
    s=z3.Solver();s.set(timeout=int(1000*seconds))
    a=[[z3.RealVal(0),z3.RealVal(0)]]+[
        [z3.Real(f'a_{i}_{j}') for j in range(2)] for i in range(1,h)]
    b=[[z3.Real(f'b_{i}_{j}') for j in range(2)] for i in range(h)]
    s.add(*(a[i][0]==b[i][0] for i in range(h)))
    s.add(*(a[i][0]<=a[i+1][0] for i in range(1,h-1)))
    value=lambda row,w:row[0]+w*row[1]
    for w in range(1,n):
        perm=[z3.Int(f'p_{w}_{i}') for i in range(h)]
        s.add(z3.Distinct(perm))
        for i in range(h):
            s.add(0<=perm[i],perm[i]<h)
            s.add(*(z3.Implies(perm[i]==j,value(a[i],w)==value(b[j],w))
                    for j in range(h)))
    av=[value(row,n) for row in a];bv=[value(row,n) for row in b]
    s.add(z3.Sum([z3.If(v==0,1,0) for v in av])>
          z3.Sum([z3.If(v==0,1,0) for v in bv]))
    s.add(*(z3.Or(v==0,v>=1,v<=-1) for v in av+bv))
    start=time.monotonic();answer=s.check()
    record={'n':n,'terms_per_list':h,'answer':str(answer),
            'seconds':time.monotonic()-start,'scope':'Symmetric point gate only.'}
    if answer==z3.unknown:record['reason']=s.reason_unknown()
    if answer==z3.sat:
        model=s.model()
        def rational(v):
            q=model.eval(v,model_completion=True)
            return Fraction(q.numerator_as_long(),q.denominator_as_long())
        aa=[[rational(v) for v in row] for row in a]
        bb=[[rational(v) for v in row] for row in b]
        for w in range(n):
            assert Counter(value(row,w) for row in aa)==Counter(value(row,w) for row in bb)
        assert Counter(value(row,n) for row in aa)!=Counter(value(row,n) for row in bb)
        path=out/f'weight-switching-n{n}-h{h}.json'
        path.write_text(json.dumps({'n':n,'left':[[[v.numerator,v.denominator] for v in row] for row in aa],
            'right':[[[v.numerator,v.denominator] for v in row] for row in bb],
            'exact_checked':True,'target_proved':False})+'\n')
        record['certificate']=str(path)
    print(json.dumps(record),flush=True)
    with (out/'results.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
    return answer


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=14400)
    p.add_argument('--trial-seconds',type=float,default=600)
    args=p.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    deadline=time.monotonic()+args.seconds
    for n in range(3,10):
        for h in range(n,2*n+5):
            remaining=deadline-time.monotonic()
            if remaining<=0:return
            if trial(n,h,min(remaining,args.trial_seconds),args.out)==z3.sat:break


if __name__=='__main__':main()
