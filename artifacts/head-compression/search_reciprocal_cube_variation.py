#!/usr/bin/env python3
"""Search Boolean-only signed reciprocal identities and their variations.

The base lists must have different value multisets already at zero, and
their reciprocal difference must be nonzero at the cube center. Thus a
SAT witness would be outside both permutation identities and identities
of rational functions on an open set. All positive witnesses are checked
exactly and compiled with a rational perturbation error bound. No timeout
or bounded UNSAT result is an unrestricted lower bound. Run through heavy.
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


def solve(n,m,slope_bound,constant_bound,seconds,seed,out):
    started=time.monotonic()
    points=list(itertools.product((0,1),repeat=n))
    rng=random.Random(seed)
    labels=[rng.choice((-1,1)) for _ in points]
    rows=[[z3.Int(f'D_{h}_{i}') for i in range(n+1)] for h in range(2*m)]
    directions=[[z3.Real(f'a_{h}_{i}') for i in range(n+1)] for h in range(2*m)]
    bias=z3.Real('bias')
    solver=z3.SolverFor('QF_LIRA')
    solver.set(timeout=int(1000*seconds),random_seed=seed)
    solver.add(*[z3.And(1<=row[0],row[0]<=constant_bound) for row in rows])
    solver.add(*[z3.And(1<=v,v<=slope_bound) for row in rows for v in row[1:]])
    # Sort each side at the zero vertex; duplicate constants are permitted.
    for start in (0,m):
        solver.add(*[rows[h][0]<=rows[h+1][0] for h in range(start,start+m-1)])
    solver.add(z3.Or([z3.Sum([z3.If(row[0]==rows[h][0],1,0) for row in rows[:m]]) !=
                     z3.Sum([z3.If(row[0]==rows[h][0],1,0) for row in rows[m:]])
                     for h in range(m)]))
    for vertex,(x,y) in enumerate(zip(points,labels)):
        base,leading=[],[]
        for h,(row,direction) in enumerate(zip(rows,directions)):
            d=affine(row,x);numerator=affine(direction,x)
            base_value=z3.Real(f'q_{vertex}_{h}')
            derivative=z3.Real(f'r_{vertex}_{h}')
            choices=[z3.And(d==k,k*base_value==1,k*k*derivative==numerator)
                     for k in range(1+sum(x),constant_bound+slope_bound*sum(x)+1)]
            solver.add(z3.Or(choices))
            sign=1 if h<m else -1
            base.append(sign*base_value)
            leading.append(-sign*derivative)
        solver.add(z3.Sum(base)==0,y*(bias+z3.Sum(leading))>=1)
    center=[]
    for h,row in enumerate(rows):
        twice=2*row[0]+z3.Sum(row[1:])
        value=z3.Real(f'center_{h}')
        solver.add(z3.Or([z3.And(twice==k,k*value==2)
                         for k in range(2+n,2*constant_bound+n*slope_bound+1)]))
        center.append((1 if h<m else -1)*value)
    solver.add(z3.Sum(center)!=0)
    print(json.dumps({'event':'solver-start','n':n,'heads':2*m,'roots_per_side':m,
                      'slope_bound':slope_bound,'constant_bound':constant_bound,
                      'setup_seconds':time.monotonic()-started}),flush=True)
    status=solver.check()
    result={'n':n,'heads':2*m,'roots_per_side':m,'slope_bound':slope_bound,
            'constant_bound':constant_bound,'seed':seed,'status':str(status),
            'seconds':time.monotonic()-started,'target_proved':False,
            'unrestricted_lower_bound':False,'labels_lexicographic':labels}
    if status==z3.sat:
        model=solver.model()
        ds=[[model.eval(t).as_long() for t in row] for row in rows]
        aa=[[rational(model,t) for t in row] for row in directions]
        c=rational(model,bias)
        u,v=ds[:m],ds[m:];a,b=aa[:m],aa[m:]
        assert sorted(row[0] for row in u)!=sorted(row[0] for row in v)
        assert all(min(row)>0 for row in ds)
        assert all(sum(Fraction(1,affine(row,x)) for row in u)==
                   sum(Fraction(1,affine(row,x)) for row in v) for x in points)
        center_value=sum(Fraction(2,2*row[0]+sum(row[1:])) for row in u)-\
                     sum(Fraction(2,2*row[0]+sum(row[1:])) for row in v)
        assert center_value!=0
        result.update(u=u,v=v,a=[list(map(str,row)) for row in a],
                      b=[list(map(str,row)) for row in b],bias=str(c),
                      center_difference=str(center_value),exact_base_vertices_checked=1<<n)
        certificate=compile_affine_variation(u,v,a,b,c,labels)
        path=out/'certificate.json';path.write_text(json.dumps(certificate)+'\n')
        result['certificate_audit']=verify(path)
        result['certificate']='certificate.json'
    elif status==z3.unknown:
        result['reason_unknown']=solver.reason_unknown()
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in
                     ['u','v','a','b','labels_lexicographic','certificate_audit']}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--n',type=int,required=True)
    p.add_argument('--roots',type=int,required=True)
    p.add_argument('--slope-bound',type=int,default=2)
    p.add_argument('--constant-bound',type=int,default=12)
    p.add_argument('--seconds',type=float,default=14400)
    p.add_argument('--seed',type=int,default=2026112315)
    p.add_argument('--out',type=Path,required=True)
    args=p.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    assert args.n>=1 and args.roots>=1 and args.slope_bound>=1 and args.constant_bound>=1
    solve(args.n,args.roots,args.slope_bound,args.constant_bound,args.seconds,args.seed,args.out)
