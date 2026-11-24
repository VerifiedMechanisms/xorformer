#!/usr/bin/env python3
"""Check a common eight-pole biased residue germ for all butterfly targets.

No LP solver is used. First enumerate the symbolic comparison profiles;
then solve the supplied rational-function basis by exact power series.
"""
from pathlib import Path
import importlib.util
import itertools
import json
import sys
from flint import fmpq_series as S,ctx

path=Path(__file__).parent
spec=importlib.util.spec_from_file_location('bf',path/'butterfly-rectangle-decoder-check.py')
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)
data=json.loads(Path(sys.argv[1]).read_text()) if len(sys.argv)>1 else json.loads((path/'butterfly-adaptive-haar-common-h8-laurent.json').read_text())
d=data['dimension'];H=1<<d;sw=bf.switches(d);blocks=list(dict.fromkeys((k,g) for k,s,g in sw))
profiles=set()
for bits in itertools.product((0,1),repeat=len(sw)):
    pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)]
    for k,g in blocks:
        pos=[s for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==0]
        neg=[s for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==1]
        for a in pos:
            for b in neg:
                j=next(j for j in range(d) if ((a>>j)&1)!=((b>>j)&1))
                sign=1 if (a>>j)&1 else -1
                u=tuple(sign*(0 if inv[y]>>(k+1)!=g else 1 if not inv[y]&(1<<k) else -1) for y in range(H))
                profiles.add((min(a,b),max(a,b),u))
canonical={(min(a,b),max(a,b),tuple(u)) for a,b,u in data['rows']}
assert canonical==profiles and len(profiles)==len(data['rows'])==40

ctx.cap=data.get('precision',128);shift=ctx.cap//3;x=S([0,1])
p=[sum((x**data['powers'][j] for j in range(d) if y&(1<<j)),S([])) for y in range(H)]
def row(spec):
    a,b,u=spec
    return [u[y]/((1-p[a]-p[y])*(1-p[b]-p[y])) for y in range(H)]
basis=[row(data['rows'][i]) if i<len(data['rows']) else [S([int(j==i-len(data['rows']))]) for j in range(H)] for i in data['basis']]
assert len(basis)==H
A=[values+[x**shift] for values in basis];columns=list(range(H));pivots=[]
for k in range(H):
    valuation,i,j=min((A[i][j].valuation(),i,j) for i in range(k,H) for j in range(k,H) if A[i][j].valuation()>=0)
    assert all(A[ii][jj].valuation()>=0 or A[ii][jj].prec>=valuation for ii in range(k,H) for jj in range(k,H))
    pivots.append(valuation);A[k],A[i]=A[i],A[k]
    for values in A:values[k],values[j]=values[j],values[k]
    columns[k],columns[j]=columns[j],columns[k];pivot=A[k][k]
    assert all((v.prec>=valuation if v.valuation()<0 else v.valuation()>=valuation) for v in A[k])
    A[k]=[v/pivot for v in A[k]]
    for i in range(H):
        if i!=k:
            multiplier=A[i][k]
            A[i]=[v-multiplier*w for v,w in zip(A[i],A[k])]
c=[None]*H
for k in range(H):c[columns[k]]=A[k][-1]
for values in basis:
    residual=sum((a*b for a,b in zip(values,c)),S([]))-x**shift
    assert residual.valuation()<0 and residual.prec>0
leading=[[v.valuation()-shift,str(v[v.valuation()])] for v in c]
if 'leading' in data:assert leading==data['leading']
if 'pivots' in data:assert pivots==data['pivots']
if data.get('require_positive_residues'):assert all(v.valuation()>=0 and v[v.valuation()]>0 for v in c)
for spec in data['rows']:
    score=sum((a*b for a,b in zip(row(spec),c)),S([]));valuation=score.valuation()
    assert 0<=valuation<score.prec and score[valuation]>0
print(json.dumps(dict(targets=1<<len(sw),symbolic_comparisons=len(profiles),pivots=pivots,leading=leading,status='all comparisons positive for every sufficiently small positive epsilon')))
