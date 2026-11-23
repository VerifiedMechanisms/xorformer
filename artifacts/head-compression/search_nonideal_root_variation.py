#!/usr/bin/env python3
"""Probe nonideal variations of moving-root Boolean identities.

Unlike ideal product differences, the leading logarithmic derivative here
may have conflicting Laplace signs. A SAT witness is checked with exact
rationals and compiled to ordinary positive-slope affine heads. Finite
diagnostics do not imply the universal bound. Run through heavy.
"""
import argparse
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import random
import time

import z3

from search_moving_root_identities import affine, minimum, rational, verify_identity
from verify_certificate import verify


def compile_score(u, v, a, b, bias, bound, labels):
    n, m = len(u[0])-1, len(u)
    common = [bound+1]*(n+1)
    ub = [[c+d for c,d in zip(common,row)] for row in u]
    vb = [[c+d for c,d in zip(common,row)] for row in v]
    return compile_affine_variation(ub,vb,a,b,bias,labels)


def compile_affine_variation(ub, vb, a, b, bias, labels):
    """Compile any exactly cancelling base lists, not only root permutations."""
    ub, vb, a, b = [[[Fraction(t) for t in row] for row in rows]
                    for rows in (ub, vb, a, b)]
    bias = Fraction(bias)
    n = len(ub[0])-1
    assert all(len(row)==n+1 for row in ub+vb+a+b)
    assert all(min(row)>0 for row in ub+vb)
    points = list(itertools.product((0,1),repeat=n))
    assert len(labels)==len(points)
    assert len(ub)==len(a) and len(vb)==len(b)
    assert all(sum(Fraction(1,affine(d,x)) for d in ub)==
               sum(Fraction(1,affine(d,x)) for d in vb) for x in points)
    values = [bias-sum(affine(r,x)/affine(d,x)**2 for r,d in zip(a,ub))
                  +sum(affine(r,x)/affine(d,x)**2 for r,d in zip(b,vb)) for x in points]
    margin = min(y*s for y,s in zip(labels,values))
    assert margin>=1
    # The exact first-order remainder is eps*a^2/[B^2*(B+eps*a)].
    epsilon = Fraction(1)
    while True:
        coefficients_positive = all(c+epsilon*t>0 for row,delta in zip(ub+vb,a+b)
                                    for c,t in zip(row,delta))
        if coefficients_positive:
            error = max(sum(epsilon*affine(delta,x)**2 /
                            (affine(row,x)**2*(affine(row,x)+epsilon*affine(delta,x)))
                            for row,delta in zip(ub+vb,a+b)) for x in points)
            if error < margin/2:
                break
        epsilon /= 2
    heads=[]
    for sign,rows,delta in [(1,ub,a),(-1,vb,b)]:
        for row,direction in zip(rows,delta):
            denominator=[c+epsilon*d for c,d in zip(row,direction)]
            numerator=[Fraction(sign)/epsilon]+[Fraction(0)]*n
            scale=math.lcm(*(q.denominator for q in numerator+denominator))
            heads.append({'numerator':[int(q*scale) for q in numerator],
                          'denominator':[int(q*scale) for q in denominator]})
    # Certificate convention uses bit i as the ith little-endian input bit.
    label_map=dict(zip(points,labels))
    little_labels=[label_map[tuple((vertex>>i)&1 for i in range(n))]
                   for vertex in range(1<<n)]
    return {'n':n,'labels':little_labels,'heads':heads,
            'bias':[bias.numerator,bias.denominator],
            'scope':'One finite nonideal root-variation witness, not a universal result.',
            'variation_epsilon':str(epsilon),'variation_margin':str(margin),
            'variation_error_bound':str(error)}


def solve(n,m,bound,seconds,seed,out):
    start=time.monotonic()
    points=list(itertools.product((0,1),repeat=n))
    rng=random.Random(seed)
    labels=[rng.choice((-1,1)) for _ in points]
    u=[[h]+[z3.Int(f'u_{h}_{i}') for i in range(n)] for h in range(m)]
    v=[[h]+[z3.Int(f'v_{h}_{i}') for i in range(n)] for h in range(m)]
    a=[[z3.Real(f'a_{h}_{i}') for i in range(n+1)] for h in range(m)]
    b=[[z3.Real(f'b_{h}_{i}') for i in range(n+1)] for h in range(m)]
    bias=z3.Real('bias')
    solver=z3.SolverFor('QF_LIRA')
    solver.set(timeout=int(1000*seconds),random_seed=seed)
    solver.add(*[z3.And(-bound<=t,t<=bound) for row in u+v for t in row[1:]])
    solver.add(*[t==0 for t in u[0][1:]])
    all_values=[]
    for vertex,(x,y) in enumerate(zip(points,labels)):
        ur,vr=[affine(row,x) for row in u],[affine(row,x) for row in v]
        all_values.append((x,ur,vr))
        solver.add(z3.Distinct(ur),z3.Distinct(vr))
        solver.add(*[z3.Or([r==s for s in vr]) for r in ur])
        common=(bound+1)*(1+sum(x))
        terms=[]
        for side,(roots,directions) in enumerate([(ur,a),(vr,b)]):
            for h,(root,direction) in enumerate(zip(roots,directions)):
                term=z3.Real(f'q_{vertex}_{side}_{h}')
                numerator=affine(direction,x)
                choices=[]
                for k in range(h-bound*sum(x),h+bound*sum(x)+1):
                    assert common+k>0
                    choices.append(z3.And(root==k,(common+k)**2*term==numerator))
                solver.add(z3.Or(choices))
                terms.append((-1 if side==0 else 1)*term)
        solver.add(y*(bias+z3.Sum(terms))>=1)
    mins={x:minimum(ur) for x,ur,_ in all_values}
    square=[tuple([i,j]+[0]*(n-2)) for i,j in [(0,0),(1,0),(0,1),(1,1)]]
    solver.add(mins[square[0]]-mins[square[1]]-mins[square[2]]+mins[square[3]]!=0)
    edges=[[z3.Or([ur[h]==vr[k] for _,ur,vr in all_values]) for k in range(m)]
           for h in range(m)]
    distance=[z3.Int(f'd_{j}') for j in range(2*m)]
    solver.add(distance[0]==0)
    for j in range(1,2*m):
        solver.add(distance[j]>=1,distance[j]<2*m)
        neighbors=([(m+k,edges[j][k]) for k in range(m)] if j<m else
                   [(h,edges[h][j-m]) for h in range(m)])
        solver.add(z3.Or([z3.And(edge,distance[k]<distance[j]) for k,edge in neighbors]))
    setup=time.monotonic()-start
    print(json.dumps({'event':'solver-start','n':n,'roots':m,'heads':2*m,
                      'bound':bound,'seed':seed,'setup_seconds':setup}),flush=True)
    status=solver.check()
    result={'n':n,'roots':m,'heads':2*m,'bound':bound,'seed':seed,
            'status':str(status),'seconds':time.monotonic()-start,
            'target_proved':False,'unrestricted_lower_bound':False,
            'labels_lexicographic':labels}
    if status==z3.sat:
        model=solver.model()
        uu=[[row[0]]+[model.eval(t).as_long() for t in row[1:]] for row in u]
        vv=[[row[0]]+[model.eval(t).as_long() for t in row[1:]] for row in v]
        aa=[[rational(model,t) for t in row] for row in a]
        bb=[[rational(model,t) for t in row] for row in b]
        c=rational(model,bias)
        result.update(u=uu,v=vv,a=[list(map(str,row)) for row in aa],
                      b=[list(map(str,row)) for row in bb],bias=str(c),
                      identity_audit=verify_identity(uu,vv))
        certificate=compile_score(uu,vv,aa,bb,c,bound,labels)
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
    p.add_argument('--bound',type=int,default=3)
    p.add_argument('--seconds',type=float,default=14400)
    p.add_argument('--seed',type=int,default=2026112315)
    p.add_argument('--out',type=Path,required=True)
    args=p.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    assert args.n>=2 and args.roots>=2 and args.bound>=1
    solve(args.n,args.roots,args.bound,args.seconds,args.seed,args.out)
