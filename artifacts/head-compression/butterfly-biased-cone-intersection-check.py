#!/usr/bin/env python3
"""Four biased Haar target cones: all pairwise intersections exist, joint empty.

Exact rational checks at the specified finite scale. No solver is used.
The empty common intersection is not an obstruction to target-adaptive
residues or to the original HeadComplexity model.
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import json

path=Path(__file__).parent
spec=importlib.util.spec_from_file_location('bf',path/'butterfly-rectangle-decoder-check.py')
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)
data=json.loads((path/'butterfly-biased-cone-intersection.json').read_text())
d=data['dimension'];H=1<<d;epsilon=F(data['epsilon']);sw=bf.switches(d)
blocks=list(dict.fromkeys((k,g) for k,s,g in sw))
p=[sum((epsilon**data['powers'][j] for j in range(d) if y&(1<<j)),F(0)) for y in range(H)]
def comparisons(bits):
    pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)];rows=[]
    for k,g in blocks:
        pos=[s for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==0]
        neg=[s for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==1]
        for a in pos:
            for b in neg:
                sign=1 if p[a]>p[b] else -1
                rows.append([F(sign*(0 if inv[y]>>(k+1)!=g else 1 if not inv[y]&(1<<k) else -1))/((1-p[a]-p[y])*(1-p[b]-p[y])) for y in range(H)])
    return rows
rows_by_target=[comparisons(bits) for bits in data['targets']]
allrows=sum(rows_by_target,[]);dual=[F(0)]*len(allrows)
for index,value in data['dual']:dual[index]=F(value)
assert all(v>=0 for v in dual) and sum(dual)==1
assert all(sum(dual[i]*allrows[i][j] for i in range(len(dual)))==0 for j in range(H))
for pair in data['pairs']:
    c=list(map(F,pair['c']))
    for index in pair['indices']:
        assert all(sum(a*b for a,b in zip(row,c))>0 for row in rows_by_target[index])
        bits=data['targets'][index];pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)]
        values=[sum((F(0 if inv[y]>>(k+1)!=g else 1 if not inv[y]&(1<<k) else -1)*c[y]/(1-p[s]-p[y]) for y in range(H)),F(0)) for k,s,g in sw]
        for k,g in blocks:
            pos=[e for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==0]
            neg=[e for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==1]
            if pos and neg:bias=-(min(values[e] for e in pos)+max(values[e] for e in neg))/2
            elif pos:bias=1-min(values[e] for e in pos)
            else:bias=-1-max(values[e] for e in neg)
            assert all((1-2*bits[e])*(values[e]+bias)>0 for e in pos+neg)
assert len(data['pairs'])==6 and len(data['dual'])==17
print(json.dumps(dict(dimension=d,nonempty_pair_intersections=6,empty_joint_intersection=True,dual_support=len(data['dual']),strict_original_queries=6*2*len(sw))))
