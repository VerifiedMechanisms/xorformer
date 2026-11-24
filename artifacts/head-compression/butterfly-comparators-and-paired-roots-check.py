#!/usr/bin/env python3
"""Exact checks for comparison routing and two-root interpolation."""
from fractions import Fraction as F
from itertools import product
from functools import reduce
import importlib.util
from pathlib import Path
import random
import json

path=Path(__file__).with_name('butterfly-rectangle-decoder-check.py')
spec=importlib.util.spec_from_file_location('bf',path)
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)
comparisons=0
for d in range(1,4):
    H=2**d;sw=bf.switches(d)
    for bits in product((0,1),repeat=len(sw)):
        pi=bf.permutation(d,bits)
        values=[sum(((pi[h]>>j)&1)*2**(d-1-j) for j in range(d)) for h in range(H)]
        for setting,(k,s,g) in zip(bits,sw):
            h=(g<<(k+1))+s;hp=h+(1<<k)
            assert (values[h]>values[hp])==bool(setting)
            if setting:values[h],values[hp]=values[hp],values[h]
            comparisons+=1

def mul(values):return reduce(lambda a,b:a*b,values,F(1))
def interpolate(xs,ps,ys):
    assert len(xs)==len(ps)==len(ys)
    return [sum((ys[i]*mul(xs[i]-p for p in ps)*
                 mul((p-xs[k])/(xs[i]-xs[k]) for k in range(len(xs)) if k!=i)
                 for i in range(len(xs))),F(0))/mul(p-z for z in ps if z!=p)
            for p in ps]
def evaluate(xs,ps,cs):return [sum((c/(x-p) for p,c in zip(ps,cs)),F(0)) for x in xs]

rng=random.Random(52631);rootcases=0
for q in range(1,9):
    t=[1+F(i,q+1) for i in range(q)]
    poles=[[F(2*h+b+1,100*q) for b in range(2)] for h in range(q)]
    words=list(product((-1,1),repeat=q))
    cases=product(words,repeat=2) if q<=4 else ((rng.choice(words),rng.choice(words)) for _ in range(24))
    for sigma,tau0 in cases:
        tau=list(tau0)
        if sum(x==y for x,y in zip(sigma,tau))<q/2:tau=[-y for y in tau]
        I=[i for i in range(q) if sigma[i]==tau[i]];J=[i for i in range(q) if sigma[i]!=tau[i]]
        pi=[p for h in I for p in poles[h]][:q]
        ci=interpolate(t,pi,[F(sigma[i] if i in I else 0) for i in range(q)])
        vi=evaluate(t,pi,ci)
        pj=[poles[h][0] for h in J]
        cj=interpolate([t[h] for h in J],pj,[F(sigma[h]) for h in J]) if J else []
        vj=evaluate(t,pj,cj)
        L=1+max(abs(vj[i]) for i in I)
        assert all(sigma[i]*(L*vi[i]+vj[i])>0 for i in range(q))
        assert all(tau[i]*(L*vi[i]-vj[i])>0 for i in range(q))
        rootcases+=1
constant_checks=0
for q in range(1,10):
    p=[F(i+1,100*q) for i in range(q)]
    c=[-mul(p[h]-(1-z) for z in p)/mul(p[h]-z for z in p if z!=p[h]) for h in range(q)]
    assert all(value==1 for value in evaluate([1-z for z in p],p,c))
    assert all(c[h]*(-1)**h>0 for h in range(q))
    constant_checks+=q
print(json.dumps(dict(exact_comparisons=comparisons,paired_root_cases=rootcases,
                      inverse_constant_entries=constant_checks)))
