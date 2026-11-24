"""Independent standard-library verification of all pure and vanilla signs."""
import argparse
from fractions import Fraction as Q
import itertools
import json
from pathlib import Path


def verify(rec):
    n=rec['n'];p=rec['pure_certificate'];v=rec['vanilla_certificate'];truth=int(p['truth_table'],16)
    assert truth==int(v['truth_table'],16)
    atoms=[]
    for row in p['atoms']:
        q={key:[Q(*a) for a in value] if key in ['a','b'] else Q(*value) for key,value in row.items()}
        assert q['gamma']>0 and all(a>0 for a in q['a']+q['b'])
        atoms.append(q)
    dd=v['denominators']; nn=v['numerators']; assert len(dd)==len(nn)==len(atoms)==3
    for d in dd:
        assert len(d)==n+1 and d[0]>sum(abs(a) for a in d[1:])
        assert all(a>0 for a in d[1:]) or all(a<0 for a in d[1:])
    margin=None
    for mask in range(1<<n):
        bits=[(mask>>i)&1 for i in range(n)];z=[2*x-1 for x in bits];y=1 if (truth>>mask)&1 else -1
        score=Q(*p['constant'])
        for a in atoms:
            d=a['gamma']+sum(a['b'][i] if bits[i] else a['a'][i] for i in range(n))
            num=a['eta']+sum(a['b'][i]*a['v1'] if bits[i] else a['a'][i]*a['v0'] for i in range(n))
            score+=num/d
        assert y*score>0
        ds=[d[0]+sum(a*b for a,b in zip(d[1:],z)) for d in dd]
        ns=[a[0]+sum(b*c for b,c in zip(a[1:],z)) for a in nn]
        val=y*sum(ns[h]*ds[(h+1)%3]*ds[(h+2)%3] for h in range(3))
        assert val>0
        margin=val if margin is None else min(margin,val)
    assert margin==v['minimum_integer_cleared_margin']
    assert p['globally_complement_invariant']==all(((truth>>x)&1)==((truth>>((1<<n)-1-x))&1) for x in range(1<<n))
    return 1<<n


def main():
    ap=argparse.ArgumentParser();ap.add_argument('file',type=Path);a=ap.parse_args()
    records=[json.loads(line) for line in a.file.read_text().splitlines()]
    count=sum(verify(r) for r in records)
    print(f'Verified {len(records)} exact pure/vanilla three-head pairs on {count} cube inputs.')
    print(f'Changed baseline zero sets: {sum(r["pure_certificate"]["baseline_zero_vertices"]>0 for r in records)}.')

if __name__=='__main__':main()
