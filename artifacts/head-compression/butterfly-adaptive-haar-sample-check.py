#!/usr/bin/env python3
"""Verify sampled biased adaptive Haar witnesses using exact rationals.

This is evidence about the listed targets, not a universality theorem.
No LP solver is imported. The generation script uses pplpy's exact
continuous LP solver, and every returned witness is checked here in the
original, biased query system rather than only its reduced inequalities.
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import json
import sys
sys.set_int_max_str_digits(0)

spec=importlib.util.spec_from_file_location('bf',Path(__file__).with_name('butterfly-rectangle-decoder-check.py'))
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)
path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('butterfly-adaptive-haar-h32-sample.json')
data=json.loads(path.read_text());d=data['dimension'];H=1<<d
sw=bf.switches(d);blocks=list(dict.fromkeys((k,g) for k,s,g in sw))
epsilon=F(data['epsilon']);powers=data['powers']
p=[sum((epsilon**powers[j] for j in range(d) if y&(1<<j)),F(0)) for y in range(H)]
assert all(1-p[s]-p[y]>0 for k,s,g in sw for y in range(H))
checked=0
for rec in data['witnesses']:
    bits=rec['bits'];assert len(bits)==len(sw) and all(b in (0,1) for b in bits)
    c=list(map(F,rec['c']));assert len(c)==H
    pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)]
    values=[]
    for k,s,g in sw:
        values.append(sum((F(0 if inv[y]>>(k+1)!=g else
                   1 if not inv[y]&(1<<k) else -1)*c[y]/(1-p[s]-p[y])
                   for y in range(H)),F(0)))
    for block in blocks:
        pos=[values[e] for e,(k,s,g) in enumerate(sw) if (k,g)==block and bits[e]==0]
        neg=[values[e] for e,(k,s,g) in enumerate(sw) if (k,g)==block and bits[e]==1]
        if pos and neg:
            assert min(pos)>max(neg)
            bias=-(min(pos)+max(neg))/2
        elif pos:bias=1-min(pos)
        else:bias=-1-max(neg)
        for e,(k,s,g) in enumerate(sw):
            if (k,g)==block:
                assert (1-2*bits[e])*(values[e]+bias)>0
                checked+=1
print(json.dumps(dict(dimension=d,targets=len(data['witnesses']),strict_queries=checked,
                      status='exact finite sample, not universal')))
