#!/usr/bin/env python3
"""Independently verify finite orthant-pair matching certificates exactly."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


def verify(path):
    raw=path.read_bytes();data=json.loads(raw)
    vectors=data['vectors'];k=len(vectors[0]);count=len(vectors)
    assert k>=1 and all(len(row)==k for row in vectors)
    assert all(isinstance(v,int) for row in vectors for v in row)
    matchings=data['matchings'];target=data['target']
    assert len(matchings)==1<<(k-1)
    minimum=None
    for code,matching in enumerate(matchings):
        assert len(matching)>=target
        used=set()
        for a,b,num,den,orientation in matching:
            assert 0<=a<count and 0<=b<count and a!=b
            assert a not in used and b not in used
            assert den>0 and orientation in [-1,1]
            used.update([a,b]);lam=Fraction(num,den)
            for j in range(k):
                sign=1 if code>>j&1 else -1
                margin=sign*orientation*(vectors[a][j]+lam*vectors[b][j])
                assert margin>0
                minimum=margin if minimum is None else min(minimum,margin)
    return {'file':str(path),'sha256':hashlib.sha256(raw).hexdigest(),
        'k':k,'dictionary_size':count,'orthant_pairs':len(matchings),
        'matching_size_at_least':target,'minimum_exact_margin_positive':minimum>0,
        'scope':'Finite shared vector dictionary only; no Boolean head bound.'}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('files',nargs='+',type=Path)
    for path in p.parse_args().files:
        print(json.dumps(verify(path)),flush=True)
