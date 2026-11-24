#!/usr/bin/env python3
"""Exact eight-wire adaptive-residue certificate, with active bases.

Run as `heavy python3 ... --generate` to regenerate the rational LP
witnesses, or without arguments to verify the saved certificate.
The written integer-polynomial bound extends these witnesses to all
smaller positive hierarchy scales; no growing-capacity claim is made.
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import itertools
import json
import sys

path=Path(__file__).with_name('butterfly-rectangle-decoder-check.py')
spec=importlib.util.spec_from_file_location('bf',path)
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)
output=Path(__file__).with_suffix('.json')
H=8;d=3;sw=bf.switches(d);eps=F(1,2**240)
poles=[sum((eps**(j+1) for j in range(d) if y&(1<<j)),F(0)) for y in range(H)]

def matrix(bits):
    pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)]
    return [[F((1-2*bits[e])*(0 if inv[y]>>(k+1)!=g else
                1 if not inv[y]&(1<<k) else -1),1)/(1-poles[s]-poles[y])
             for y in range(H)] for e,(k,s,g) in enumerate(sw)]

def dot(a,b):return sum((x*y for x,y in zip(a,b)),F(0))

def solve(rows, rhs):
    a=[list(row)+[v] for row,v in zip(rows,rhs)]
    for j in range(H):
        pivot=next(i for i in range(j,H) if a[i][j])
        a[j],a[pivot]=a[pivot],a[j];v=a[j][j]
        a[j]=[x/v for x in a[j]]
        for i in range(H):
            if i!=j:
                v=a[i][j]
                if v:a[i]=[x-v*y for x,y in zip(a[i],a[j])]
    return [row[-1] for row in a]

def rank(rows):
    a=[list(row) for row in rows];rank=0
    for j in range(H):
        pivot=next((i for i in range(rank,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[rank],a[pivot]=a[pivot],a[rank];v=a[rank][j]
        a[rank]=[x/v for x in a[rank]]
        for i in range(rank+1,len(a)):
            v=a[i][j]
            if v:a[i]=[x-v*y for x,y in zip(a[i],a[rank])]
        rank+=1
        if rank==H:break
    return rank

if '--generate' in sys.argv:
    from sympy import Matrix,Rational as Q
    from sympy.solvers.simplex import linprog
    witnesses=[]
    for ix,tail in enumerate(itertools.product((0,1),repeat=8)):
        bits=(0,0,0,0)+tail;A=matrix(bits)
        S=Matrix([[Q(v.numerator,v.denominator) for v in row] for row in A])
        _,x=linprog([0]*H,-S,[-1]*len(sw),bounds=(1,None))
        c=[F(int(v.p),int(v.q)) for v in x]
        assert min(c)>=1 and min(dot(row,c) for row in A)>=1
        constraints=A+[[F(int(i==j)) for j in range(H)] for i in range(H)]
        active=[i for i,row in enumerate(constraints) if dot(row,c)==1]
        basis=[]
        for i in active:
            if rank([constraints[j] for j in basis+[i]])>len(basis):basis.append(i)
            if len(basis)==H:break
        assert len(basis)==H
        witnesses.append(dict(tail=list(tail),basis=basis))
        if ix%32==31:print('generated',ix+1,flush=True)
    output.write_text(json.dumps(dict(epsilon=str(eps),witnesses=witnesses),indent=2)+'\n')

saved=json.loads(output.read_text());assert saved['epsilon']==str(eps)
assert len(saved['witnesses'])==256
assert {tuple(r['tail']) for r in saved['witnesses']}==set(itertools.product((0,1),repeat=8))
scores=0
for record in saved['witnesses']:
    tail=tuple(record['tail']);A=matrix((0,0,0,0)+tail)
    constraints=A+[[F(int(i==j)) for j in range(H)] for i in range(H)]
    selected=[constraints[i] for i in record['basis']]
    assert rank(selected)==H
    c=solve(selected,[F(1)]*H)
    assert min(c)>0 and all(dot(row,c)==1 for row in selected)
    assert all(dot(row,c)>0 for row in A)
    # The signed matrix is exactly independent of the bottom switch bits.
    for bottom in itertools.product((0,1),repeat=4):
        assert matrix(bottom+tail)==A
        scores+=len(sw)
print(json.dumps(dict(positive_witnesses=256,strict_scores=scores,
                      independent_active_bases=256,epsilon=str(eps))))
