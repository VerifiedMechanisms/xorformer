#!/usr/bin/env python3
"""Exact Laurent continuation of a specified biased Haar target.

Requires python-flint. It uses exact rational power series with precision
tracking, not floating point arithmetic or a feasibility solver. Every
nonzero pivot and every strict score has a certified nonzero leading term.
Run through `heavy` when processing many certificates.
"""
import argparse
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import json
import sys
from flint import fmpq_series as Series, ctx
sys.set_int_max_str_digits(0)

parser=argparse.ArgumentParser()
parser.add_argument('certificate',nargs='?',default=str(Path(__file__).with_name('butterfly-adaptive-haar-h32-laurent.json')))
parser.add_argument('--precision',type=int,default=256)
parser.add_argument('--index',type=int,default=0)
parser.add_argument('--summary',action='store_true')
args=parser.parse_args()
data=json.loads(Path(args.certificate).read_text())
if 'certificates' in data:data=data['certificates'][args.index]
K=args.precision; M=K//3; ctx.cap=K
spec=importlib.util.spec_from_file_location('bf',Path(__file__).with_name('butterfly-rectangle-decoder-check.py'))
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)
d=data['dimension']; H=1<<d; bits=data['bits']; powers=data['powers']
sw=bf.switches(d); blocks=list(dict.fromkeys((k,g) for k,s,g in sw))
pi=bf.permutation(d,bits); inv=[pi.index(y) for y in range(H)]
x=Series([0,1]); p=[sum((x**powers[j] for j in range(d) if y&(1<<j)),Series([])) for y in range(H)]
# The first nonzero coefficient of p_a-p_b decides its sign near zero.
# The integer exponents in this certificate are distinct.
specs=[]
for k,g in blocks:
    pos=[s for i,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[i]==0]
    neg=[s for i,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[i]==1]
    for a in pos:
        for b in neg:
            difference=p[a]-p[b]; valuation=difference.valuation()
            assert valuation>=0
            sign=1 if difference[valuation]>0 else -1
            specs.append((k,g,a,b,sign))

def seriesrow(spec):
    k,g,a,b,sign=spec
    return [Series([]) if inv[y]>>(k+1)!=g else
            sign*(1 if not inv[y]&(1<<k) else -1)/((1-p[a]-p[y])*(1-p[b]-p[y]))
            for y in range(H)]

basis=[]; rhs=[]
for kind,j in data['basis']:
    assert kind in ('row','zero')
    basis.append(seriesrow(specs[j]) if kind=='row' else [Series([int(i==j)]) for i in range(H)])
    rhs.append(1 if kind=='row' else 0)
assert len(basis)==H
A=[list(row)+[x**M*value] for row,value in zip(basis,rhs)]
columns=list(range(H)); pivots=[]
# Full pivoting by valuation ensures division stays in the power-series
# ring. Multiplying the RHS by x^M handles negative Laurent exponents.
for k in range(H):
    candidates=[(A[i][j].valuation(),i,j) for i in range(k,H) for j in range(k,H)
                if A[i][j].valuation()>=0]
    assert candidates, 'Insufficient precision, or singular basis'
    valuation,i,j=min(candidates);pivots.append(valuation)
    A[k],A[i]=A[i],A[k]
    for row in A:row[k],row[j]=row[j],row[k]
    columns[k],columns[j]=columns[j],columns[k]
    pivot=A[k][k]
    assert all(v.valuation()<0 or v.valuation()>=valuation for v in A[k]), 'Increase RHS shift'
    A[k]=[v/pivot for v in A[k]]
    for i in range(H):
        if i!=k:
            multiplier=A[i][k]
            if multiplier.valuation()>=0:
                A[i]=[v-multiplier*w for v,w in zip(A[i],A[k])]
coefficients=[None]*H
for k in range(H):coefficients[columns[k]]=A[k][-1]
# Independently substitute into the uneliminated equations.
for row,value in zip(basis,rhs):
    residual=sum((a*b for a,b in zip(row,coefficients)),Series([]))-x**M*value
    assert residual.valuation()<0, 'Nonzero basis residual'
    assert residual.prec>0
leading=[]
for coefficient in coefficients:
    valuation=coefficient.valuation()
    leading.append(None if valuation<0 else [valuation-M,str(coefficient[valuation])])
score_terms=[]
for spec in specs:
    score=sum((a*b for a,b in zip(seriesrow(spec),coefficients)),Series([]))
    valuation=score.valuation()
    assert valuation>=0, 'Undecided score: increase precision'
    assert score[valuation]>0, 'Negative leading score'
    assert valuation<score.prec
    score_terms.append([valuation-M,str(score[valuation]),score.prec-M])
expected=data.get('leading_coefficients')
if expected is not None:assert leading==expected
print(json.dumps(dict(dimension=d,queries=len(sw),strict_comparisons=len(specs),
    pivots=pivots,leading_coefficients=leading,score_terms=None if args.summary else score_terms),indent=2))
