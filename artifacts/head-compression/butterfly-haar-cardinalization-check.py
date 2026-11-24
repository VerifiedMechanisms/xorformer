#!/usr/bin/env python3
"""Exact finite checks of shared-residue Haar decoding; no asymptotic claim."""
from fractions import Fraction as F
import importlib.util
import itertools
import json
from pathlib import Path

path=Path(__file__).with_name('butterfly-rectangle-decoder-check.py')
spec=importlib.util.spec_from_file_location('butterfly',path)
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)

def route(d,k,g,theta,representatives):
    choice={s:0 for s in bf.switches(d)}
    for s,b in enumerate(theta):choice[k,s,g]=b
    for s in range(1<<k):
        for b in range(2):
            current=(g<<(k+1)) | (b<<k) | s
            current ^= theta[s]<<k
            target=representatives[current&((1<<(k+1))-1)]
            for ell in range(k+1,d):
                key=(ell,current&((1<<ell)-1),current>>(ell+1))
                flip=((current^target)>>ell)&1
                # Different tracked wires have different lower k+1 bits,
                # so no later switch receives conflicting prescriptions.
                assert choice[key] in (0,flip)
                choice[key]=flip
                current ^= flip<<ell
            assert current==target
    return bf.permutation(d,[choice[s] for s in bf.switches(d)])

routing=0
for d in range(1,5):
    for k in range(d):
        for highs in itertools.product(range(1<<(d-k-1)),repeat=1<<(k+1)):
            reps=[(g<<(k+1))|a for a,g in enumerate(highs)]
            for theta in itertools.product((0,1),repeat=1<<k):
                for g in range(1<<(d-k-1)):
                    pi=route(d,k,g,theta,reps)
                    for s in range(1<<k):
                        for b in range(2):
                            h=(g<<(k+1))|(b<<k)|s
                            assert pi[h]==reps[((b^theta[s])<<k)|s]
                    routing+=1

eps=F(1,10000);T=F(99,100)
poles=[j*eps for j in range(4)]
r0=100/eps
residues=[r0,F(0),r0*(T-2*eps)/T,F(-1)]
queries=[F(1),F(1),F(1),T]
checked=0
for bits in itertools.product((0,1),repeat=4):
    pi=bf.permutation(2,bits)
    for e,(k,s,g) in enumerate(bf.switches(2)):
        t=queries[e]
        score=sum((1 if not h&(1<<k) else -1)*residues[pi[h]]/(t-poles[pi[h]])
                  for h in range(4) if h>>(k+1)==g)
        assert (1-2*bits[e])*score>0
        checked+=1
print(json.dumps(dict(routing_instances=routing,strict_four_wire_scores=checked,
                      poles=[str(v) for v in poles],residues=[str(v) for v in residues])))
