#!/usr/bin/env python3
"""Check a common H8 residue pool for all targets, with separate block biases.

The comparison certificate is exact and finite. It makes no claim about
larger butterfly trees or about arbitrarily small epsilon.
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import itertools
import json

here=Path(__file__).parent
data=json.loads((here/'butterfly-adaptive-haar-common-h8.json').read_text())
spec=importlib.util.spec_from_file_location('bf',here/'butterfly-rectangle-decoder-check.py')
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)
d=data['dimension'];H=1<<d;sw=bf.switches(d);epsilon=F(data['epsilon'])
p=[sum((epsilon**data['powers'][j] for j in range(d) if y&(1<<j)),F(0)) for y in range(H)]
c=list(map(F,data['c']));blocks=list(dict.fromkeys((k,g) for k,s,g in sw));rows=set();queries=0
assert all(1-p[s]-p[y]>0 for k,s,g in sw for y in range(H))
for bits in itertools.product((0,1),repeat=len(sw)):
    pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)]
    values=[sum((F(0 if inv[y]>>(k+1)!=g else 1 if not inv[y]&(1<<k) else -1)*c[y]/(1-p[s]-p[y]) for y in range(H)),F(0)) for k,s,g in sw]
    for k,g in blocks:
        pos=[e for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==0]
        neg=[e for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==1]
        if pos and neg:
            assert min(values[e] for e in pos)>max(values[e] for e in neg)
            bias=-(min(values[e] for e in pos)+max(values[e] for e in neg))/2
        elif pos:bias=1-min(values[e] for e in pos)
        else:bias=-1-max(values[e] for e in neg)
        for e in pos+neg:
            assert (1-2*bits[e])*(values[e]+bias)>0;queries+=1
        for a0 in pos:
            for b0 in neg:
                a=sw[a0][1];b=sw[b0][1];sg=1 if p[a]>p[b] else -1
                row=tuple(F(sg*(0 if inv[y]>>(k+1)!=g else 1 if not inv[y]&(1<<k) else -1))/((1-p[a]-p[y])*(1-p[b]-p[y])) for y in range(H))
                assert sum(v*w for v,w in zip(row,c))>=1
                rows.add(row)
assert len(rows)==data['distinct_comparisons']==40
print(json.dumps(dict(targets=1<<len(sw),strict_queries=queries,distinct_comparisons=len(rows),status='exact common residue pool at epsilon=1/100')))
