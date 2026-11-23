#!/usr/bin/env python3
"""Exact linear-arithmetic sparse search in a fixed reciprocal dictionary.

The denominator dictionary is finite. The solver selects a balanced weighted
zero relation and a strictly separating first variation on one six-bit table.
Neither success nor failure proves a universal upper or lower bound.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import json
import time
import z3
from search_moving_root_identities import affine, rational
from search_weighted_reciprocal_variation import compile_weighted
from verify_certificate import verify


def main(args):
    start=time.monotonic(); n=6
    points=list(product((0,1),repeat=n))
    labels=json.loads(Path(args.target).read_text())['labels_lexicographic']
    assert len(labels)==len(points)
    rows=[]; seen=set()
    for c in range(1,args.constant_bound+1):
        for slopes in product((1,2),repeat=n):
            key=tuple(F(v,c) for v in slopes)
            if key not in seen:
                seen.add(key); rows.append([c,*slopes])
    M=len(rows)
    solver=z3.SolverFor('QF_LRA')
    solver.set(timeout=int(args.seconds*1000),random_seed=2026112319)
    active=[z3.Bool(f'active_{j}') for j in range(M)]
    pos=[z3.Bool(f'positive_{j}') for j in range(M)]
    w=[z3.Real(f'w_{j}') for j in range(M)]
    directions=[[z3.Real(f'd_{j}_{i}') for i in range(n+1)] for j in range(M)]
    bias=z3.Real('bias')
    eps=z3.RealVal('1/10000'); cap=z3.RealVal('9/10')
    solver.add(w[0]==1,active[0],pos[0])
    for j in range(M):
        solver.add(z3.Implies(z3.Not(active[j]),z3.And(w[j]==0,*[a==0 for a in directions[j]])))
        solver.add(z3.Implies(active[j],z3.If(pos[j],w[j]>=eps,w[j]<=-eps)))
        solver.add(z3.Implies(pos[j],active[j]))
        if j: solver.add(-cap<=w[j],w[j]<=cap)
    solver.add(z3.PbLe([(a,1) for a in active],args.heads))
    solver.add(z3.PbGe([(p,1) for p in pos],2))
    solver.add(z3.PbGe([(z3.And(a,z3.Not(p)),1) for a,p in zip(active,pos)],2))
    for x,y in zip(points,labels):
        base=[]; leading=[]
        for row,weight,direction in zip(rows,w,directions):
            D=affine(row,x)
            base.append(z3.RealVal(str(F(row[0],D)))*weight)
            leading.append(affine(direction,x)/D**2)
        solver.add(z3.Sum(base)==0,y*(bias+z3.Sum(leading))>=1)
    args.out.mkdir(parents=True,exist_ok=True)
    print(json.dumps({'event':'solver-start','dictionary_size':M,'heads':args.heads,
                      'constant_bound':args.constant_bound,'setup_seconds':time.monotonic()-start}),flush=True)
    result=solver.check()
    report={'n':n,'status':str(result),'seconds':time.monotonic()-start,
            'dictionary_size':M,'heads_at_most':args.heads,'constant_bound':args.constant_bound,
            'slope_values':[1,2],'minimum_active_normalized_weight':'1/10000',
            'distinguished_normalized_weight':'1','other_normalized_weights_bound':'9/10',
            'at_least_two_weights_of_each_sign':True,'labels_lexicographic':labels,
            'target_proved':False,'unrestricted_lower_bound':False}
    if result==z3.sat:
        model=solver.model(); chosen=[j for j in range(M) if z3.is_true(model.eval(active[j]))]
        ds=[rows[j] for j in chosen]
        ws=[F(rows[j][0])*rational(model,w[j]) for j in chosen]
        aa=[[rational(model,v) for v in directions[j]] for j in chosen]
        c=rational(model,bias)
        for x,y in zip(points,labels):
            assert sum(v/affine(row,x) for row,v in zip(ds,ws))==0
            assert y*(c+sum(affine(a,x)/affine(row,x)**2 for row,a in zip(ds,aa)))>=1
        cert=compile_weighted(ds,ws,aa,c,labels)
        path=args.out/'certificate.json';path.write_text(json.dumps(cert)+'\n')
        report.update(chosen=chosen,rows=ds,weights=list(map(str,ws)),
                      directions=[list(map(str,a)) for a in aa],bias=str(c),
                      certificate_audit=verify(path))
    elif result==z3.unknown: report['reason_unknown']=solver.reason_unknown()
    (args.out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in
                     ('labels_lexicographic','directions','certificate_audit','rows','weights')}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--heads',type=int,default=8)
    p.add_argument('--constant-bound',type=int,default=4)
    p.add_argument('--seconds',type=float,default=2700)
    p.add_argument('--target',default='artifacts/head-compression/diagnostics/reciprocal-cube-n6-m4.json')
    p.add_argument('--out',type=Path,required=True)
    main(p.parse_args())
