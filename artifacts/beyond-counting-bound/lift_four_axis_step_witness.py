"""Lift an exact finite threshold-vote witness to positive-pole reciprocals."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('source',type=Path)
    ap.add_argument('output',type=Path)
    a=ap.parse_args();s=json.loads(a.source.read_text())
    assert s['solver_result']=='sat' and s['exact_finite_verified']
    h=s['heads'];m=s['queries'];base=64*h+1
    thresholds=[[0]*h for _ in range(m)]
    for axis,order in enumerate(s['orders']):
        assert sorted(order)==list(range(m))
        for rank,q in enumerate(order,1):thresholds[q][axis]=rank
    poles=[[base**(2*t) for t in row] for row in thresholds]
    residues=[[w*p for w,p in zip(gate[0],row)] for gate,row in zip(s['gates'],poles)]
    cuts=[F(gate[1],2) for gate in s['gates']]
    witnesses={};margin=None
    for mask,values in enumerate(s['comparison_witnesses']):
        x=[base**(2*sum(1-values[q][axis] for q in range(m))+1) for axis in range(h)]
        assert all(v>0 for v in x)
        for axis,order in enumerate(s['orders']):
            chain=[values[q][axis] for q in order]
            assert chain==sorted(chain)
        for q,((w,c2),p,r) in enumerate(zip(s['gates'],poles,residues)):
            ideal=sum(wi*vi for wi,vi in zip(w,values[q]))-F(c2,2)
            actual=sum(F(ri,xi+pi) for ri,xi,pi in zip(r,x,p))-cuts[q]
            sign=1 if (mask>>q)&1 else -1
            assert sign*ideal>=F(1,2)
            assert abs(actual-ideal)<=F(sum(map(abs,w)),base+1)<F(1,2)
            assert sign*actual>0
            margin=sign*actual if margin is None else min(margin,sign*actual)
        witnesses[str(mask)]=x
    out={'poles':poles,'residuals':residues,'thresholds':list(map(str,cuts)),
         'witnesses':witnesses,'patterns':2**m,'total_patterns':2**m,
         'heads':h,'queries':m,'base':base,'step_thresholds':thresholds,
         'step_weights':[v[0] for v in s['gates']],
         'step_twice_biases':[v[1] for v in s['gates']],
         'minimum_exact_signed_margin':str(margin),
         'status':'EXACT_RATIONAL_WITNESSES','main_target_proved':False}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'heads':h,'queries':m,'patterns':2**m,'exact_verified':True,
                      'minimum_margin_exceeds_one_quarter':margin>F(1,4)}))


if __name__=='__main__':main()
