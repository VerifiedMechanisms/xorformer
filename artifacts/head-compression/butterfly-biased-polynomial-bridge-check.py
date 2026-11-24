#!/usr/bin/env python3
"""Verify three finite quadratic-profile cone bridges by rational linear algebra.

No LP solver is used. These witnesses remove the saved four-target
one-dimensional bridge obstruction at its specified finite pole grid.
They do not prove a growing-depth decoder or a small-scale continuation.
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import json
from flint import fmpq_mat as Matrix, fmpq as Q
path=Path(__file__).parent
data=json.loads((path/'butterfly-biased-polynomial-bridge.json').read_text())
spec=importlib.util.spec_from_file_location('bf',path/'butterfly-rectangle-decoder-check.py')
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)
d=data['dimension'];H=1<<d;B=data['degree']+1;eps=F(data['epsilon']);sw=bf.switches(d)
blocks=list(dict.fromkeys((k,g) for k,s,g in sw))
p=[sum((eps**data['powers'][j] for j in range(d) if y&(1<<j)),F(0)) for y in range(H)]
def comparisons(bits):
    pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)];out=[]
    for k,g in blocks:
        pos=[s for e,(l,s,b) in enumerate(sw) if(l,b)==(k,g) and bits[e]==0]
        neg=[s for e,(l,s,b) in enumerate(sw) if(l,b)==(k,g) and bits[e]==1]
        for a in pos:
            for b in neg:
                sign=1 if p[a]>p[b] else -1
                out.append([F(sign*(0 if inv[y]>>(k+1)!=g else 1 if not inv[y]&(1<<k) else -1))/((1-p[a]-p[y])*(1-p[b]-p[y])) for y in range(H)])
    return out
rows=list(map(comparisons,data['targets']))
C=Matrix([[Q(str(1/(1-p[i]-p[j]))) for j in range(H)] for i in range(H)])
profiles=Matrix([[Q(str(p[i]**j)) for j in range(B)] for i in range(H)])
V=C.inv()*profiles
assert C*V==profiles
checks=0
for part in data['partitions']:
    selected=[]
    for index in part['left']+part['right']:
        for row in rows[index]:
            selected.append([Q(str(z)) for z in row]+[sum((Q(str(row[i]))*V[i,j] for i in range(H)),Q(0)) if index in part['right'] else Q(0) for j in range(B)])
    basis=[selected[i] for i in part['basis']]
    basis += [[Q(int(i==j)) for j in range(H+B)] for i in part['zero_coordinates']]
    rhs=Matrix([[1]]*len(part['basis'])+[[0]]*len(part['zero_coordinates']))
    point=Matrix(basis).inv()*rhs
    assert Matrix(basis)*point==rhs
    scores=Matrix(selected)*point
    assert all(scores[i,0]>0 for i in range(scores.nrows()))
    checks+=scores.nrows()
assert len(data['partitions'])==3 and B==3
print(json.dumps(dict(dimension=d,quadratic_profile_bridges=3,strict_comparisons=checks,status='finite exact witnesses, no induction claim')))
