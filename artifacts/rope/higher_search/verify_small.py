"""Exact full-cube verifier for pure/vanilla parity-extension pairs.
Uses only the Python standard library. These are equality certificates, not
strict separations. Every record contains a three-bit parity restriction.
"""
import argparse
from fractions import Fraction as Q
import json
import math
from pathlib import Path


def verify(rec):
    n=rec['n'];truth=int(rec['truth_table'],16);v=rec['vanilla_certificate'];dd=v['denominators'];nn=v['numerators'];margin=None;pure_margin=None
    for d in dd:
        assert len(d)==n+1 and d[0]>sum(abs(x) for x in d[1:])
        assert all(x>0 for x in d[1:]) or all(x<0 for x in d[1:])
    for a in rec['atoms']:assert a['gamma']>0 and min(a['a']+a['b'])>0
    for mask in range(1<<n):
        bits=[(mask>>i)&1 for i in range(n)];z=[2*x-1 for x in bits];y=1 if truth>>mask&1 else -1
        p=Q(*rec['constant'])+sum((Q(*a['eta'])+sum(a['b'][i]*a['v1'] if bits[i] else a['a'][i]*a['v0'] for i in range(n)))/(a['gamma']+sum(a['b'][i] if bits[i] else a['a'][i] for i in range(n))) for a in rec['atoms'])
        assert y*p>0
        pure_margin=abs(p) if pure_margin is None else min(pure_margin,abs(p))
        ds=[d[0]+sum(a*b for a,b in zip(d[1:],z)) for d in dd]
        ns=[a[0]+sum(b*c for b,c in zip(a[1:],z)) for a in nn]
        val=y*sum(ns[h]*ds[(h+1)%3]*ds[(h+2)%3] for h in range(3));assert val>0
        margin=val if margin is None else min(margin,val)
    assert margin==v['minimum_integer_cleared_margin']
    assert pure_margin==Q(*rec['minimum_margin'])
    for mask in range(8):assert (1 if truth>>mask&1 else -1)==math.prod([2*((mask>>i)&1)-1 for i in range(3)])



def main():
    ap=argparse.ArgumentParser();ap.add_argument('files',type=Path,nargs='+');a=ap.parse_args()
    records=vertices=0
    for path in a.files:
        for line in path.read_text().splitlines():
            r=json.loads(line);verify(r);records+=1;vertices+=1<<r['n']
    print({'exact_three_head_pairs':records,'cube_vertices':vertices,'parity_three_restrictions':records})

if __name__=='__main__':main()
