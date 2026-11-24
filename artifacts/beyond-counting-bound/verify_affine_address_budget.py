#!/usr/bin/env python3
"""Finite exact audits of affine-address-budget.md."""
from fractions import Fraction as F
from itertools import permutations, product
from pathlib import Path
import hashlib
import json
import math
import random

root=Path(__file__).resolve().parent
counts={"symmetry_arrays":0,"symmetry_query_families":0,
        "component_compositions":0,"tied_level_equalities":0}
rng=random.Random(20261124)

def components(n, queries):
    parent=list(range(n))
    def find(a):
        while parent[a]!=a:
            parent[a]=parent[parent[a]]; a=parent[a]
        return a
    for mask in queries:
        bits=[i for i in range(n) if mask>>i&1]
        for i in bits[1:]: parent[find(i)]=find(bits[0])
    groups={}
    for i in range(n): groups.setdefault(find(i),[]).append(i)
    return list(groups.values())

for n,h in ((3,2),(4,2),(4,3)):
    families=[list(range(1<<n)),[0]+[1<<i for i in range(n)],
              [0,1,2,3], [0,3,(1<<n)-4]]
    families += [rng.sample(range(1<<n),rng.randrange(1,1<<n)) for _ in range(16)]
    perms=list(permutations(range(h)))
    for queries in families:
        groups=components(n,queries)
        valid=0
        for sigma in product(perms,repeat=n):
            inverse=[tuple(p.index(r) for r in range(h)) for p in sigma]
            # For two different selected columns, the quadratic coefficient
            # is nonzero precisely when their parameter rows coincide.
            identity=True
            for mask in queries:
                for i in range(n):
                    for j in range(i+1,n):
                        if not(mask>>i&1 and mask>>j&1): continue
                        for r in range(h):
                            for t in range(h):
                                if ((inverse[i][r]==inverse[j][t]) != (r==t)):
                                    identity=False
            predicted=all(all(sigma[i]==sigma[group[0]] for i in group)
                          for group in groups)
            assert identity==predicted
            valid+=identity
            counts["symmetry_arrays"]+=1
        assert valid==math.factorial(h)**len(groups)
        bound=1+sum((1<<len(g))-1 for g in groups)
        assert len(set(queries))<=bound<=(1<<(n-len(groups)+1))+len(groups)-1
        counts["symmetry_query_families"]+=1

for n in range(1,18):
    for cuts in range(1<<(n-1)):
        parts=[]; last=0
        for i in range(1,n):
            if cuts>>(i-1)&1: parts.append(i-last); last=i
        parts.append(n-last)
        assert sum(1<<d for d in parts)<=(1<<(n-len(parts)+1))+2*(len(parts)-1)
        counts["component_compositions"]+=1

first=(F(1),F(3),F(7))
seconds=((first[1],first[2],first[0]),(first[2],first[0],first[1]))
for mask in range(4):
    values=[sum(F(1)/(F(2)+(first[r] if mask&1 else 0)+(second[r] if mask&2 else 0))
                for r in range(3)) for second in seconds]
    assert values[0]==values[1]
    counts["tied_level_equalities"]+=1
assert seconds[0]!=seconds[1] and len(set(first))==3

paths=(root/"affine-address-budget.md",Path(__file__).resolve())
result={"status":"PASS","scope":"finite exact checks, not Lean", "counts":counts,
        "sha256":{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}
(root/"affine-address-budget-audit.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
