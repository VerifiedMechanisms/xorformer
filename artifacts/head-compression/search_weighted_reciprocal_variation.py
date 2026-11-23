#!/usr/bin/env python3
"""Exact bounded search for weighted Boolean-only reciprocal cancellations.

The real base weights are free, and all denominator coefficients are
positive integers. A first variation is checked and compiled exactly.
This is a finite diagnostic, never an asymptotic construction or lower bound.
Run through heavy.
"""
import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import random
import time

import z3
from search_moving_root_identities import affine, rational
from search_nonideal_root_variation import compile_affine_variation
from verify_certificate import verify


def compile_weighted(rows, weights, directions, bias, labels):
    """Base sum weights[h]/rows[h] is zero; leading sum is directions/rows^2."""
    positive, negative, a, b = [], [], [], []
    for row, weight, direction in zip(rows, weights, directions):
        weight = Fraction(weight)
        assert weight != 0
        base = [Fraction(t)/abs(weight) for t in row]
        delta = [-Fraction(t)/(weight*abs(weight)) for t in direction]
        if weight > 0:
            positive.append(base); a.append(delta)
        else:
            negative.append(base); b.append(delta)
    assert positive and negative
    return compile_affine_variation(positive, negative, a, b, bias, labels)


def solve(n,H,constant_bound,seconds,seed,out):
    started=time.monotonic()
    points=list(itertools.product((0,1),repeat=n))
    rng=random.Random(seed)
    labels=[rng.choice((-1,1)) for _ in points]
    rows=[[z3.Int(f'D_{h}_{i}') for i in range(n+1)] for h in range(H)]
    weights=[z3.Real(f'w_{h}') for h in range(H)]
    directions=[[z3.Real(f'a_{h}_{i}') for i in range(n+1)] for h in range(H)]
    bias=z3.Real('bias')
    solver=z3.SolverFor('QF_LIRA')
    solver.set(timeout=int(1000*seconds),random_seed=seed)
    solver.add(*[z3.And(1<=row[0],row[0]<=constant_bound) for row in rows])
    solver.add(*[z3.And(1<=t,t<=2) for row in rows for t in row[1:]])
    solver.add(*[z3.Or(w>=1,w<=-1) for w in weights],weights[0]>=1)
    solver.add(*[rows[h][0]<=rows[h+1][0] for h in range(H-1)])
    # With slopes in {1,2}, proportional distinct rows have scale 2 or 1/2.
    for i in range(H):
        for j in range(i):
            solver.add(z3.Or([a!=b for a,b in zip(rows[i],rows[j])]))
            for s,t in [(i,j),(j,i)]:
                solver.add(z3.Or([v!=1 for v in rows[s][1:]]+
                                 [v!=2 for v in rows[t][1:]]+
                                 [2*rows[s][0]!=rows[t][0]]))
    for vertex,(x,y) in enumerate(zip(points,labels)):
        base,leading=[],[]
        for h,(row,w,direction) in enumerate(zip(rows,weights,directions)):
            D=affine(row,x); A=affine(direction,x)
            q=z3.Real(f'q_{vertex}_{h}'); r=z3.Real(f'r_{vertex}_{h}')
            solver.add(z3.Or([z3.And(D==k,k*q==w,k*k*r==A)
                       for k in range(1+sum(x),constant_bound+2*sum(x)+1)]))
            base.append(q); leading.append(r)
        solver.add(z3.Sum(base)==0,y*(bias+z3.Sum(leading))>=1)
    probe=[]
    for h,(row,w) in enumerate(zip(rows,weights)):
        scaled=(n+1)*row[0]+z3.Sum(row[1:])
        q=z3.Real(f'probe_{h}')
        solver.add(z3.Or([z3.And(scaled==k,k*q==(n+1)*w)
                   for k in range(2*n+1,(n+1)*constant_bound+2*n+1)]))
        probe.append(q)
    solver.add(z3.Sum(probe)!=0)
    print(json.dumps({'event':'solver-start','n':n,'heads':H,'constant_bound':constant_bound,
                      'setup_seconds':time.monotonic()-started}),flush=True)
    status=solver.check()
    result={'n':n,'heads':H,'constant_bound':constant_bound,'slope_values':[1,2],
            'seed':seed,'status':str(status),'seconds':time.monotonic()-started,
            'target_proved':False,'unrestricted_lower_bound':False,
            'labels_lexicographic':labels}
    if status==z3.sat:
        model=solver.model()
        ds=[[model.eval(t).as_long() for t in row] for row in rows]
        ws=[rational(model,w) for w in weights]
        aa=[[rational(model,t) for t in row] for row in directions]
        c=rational(model,bias)
        for i in range(H):
            for j in range(i):
                assert any(ds[i][k]*ds[j][0]!=ds[j][k]*ds[i][0] for k in range(1,n+1))
        assert all(sum(w/affine(row,x) for row,w in zip(ds,ws))==0 for x in points)
        probe_value=sum((n+1)*w/((n+1)*row[0]+sum(row[1:])) for row,w in zip(ds,ws))
        assert probe_value!=0
        result.update(rows=ds,weights=list(map(str,ws)),directions=[list(map(str,row)) for row in aa],
                      bias=str(c),off_cube_probe=str(probe_value),exact_base_vertices_checked=1<<n)
        certificate=compile_weighted(ds,ws,aa,c,labels)
        path=out/'certificate.json'; path.write_text(json.dumps(certificate)+'\n')
        result['certificate_audit']=verify(path)
    elif status==z3.unknown:
        result['reason_unknown']=solver.reason_unknown()
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in
                     ['rows','weights','directions','labels_lexicographic','certificate_audit']}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--n',type=int,required=True)
    p.add_argument('--heads',type=int,required=True)
    p.add_argument('--constant-bound',type=int,default=12)
    p.add_argument('--seconds',type=float,default=7200)
    p.add_argument('--seed',type=int,default=2026112315)
    p.add_argument('--out',type=Path,required=True)
    args=p.parse_args(); args.out.mkdir(parents=True,exist_ok=True)
    assert args.n>=1 and args.heads>=2 and args.constant_bound>=1
    solve(args.n,args.heads,args.constant_bound,args.seconds,args.seed,args.out)
