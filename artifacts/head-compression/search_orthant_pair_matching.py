#!/usr/bin/env python3
"""Exact certificates for disjoint vector-pair access to every orthant.

Each orthant gets its own matching in one shared integer vector dictionary.
This is only an auxiliary promised-grid decoder experiment. It does not
prove the requested Boolean head bound. Run through heavy.
"""
import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import time
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[key]='1'
import numpy as np


def run(k, multiple, seed, seconds, out):
    rng=np.random.default_rng(seed)
    m=1<<k; count=multiple*m; target=2*m; mask=m-1
    vectors=rng.integers(-1000000,1000001,(count,k),dtype=np.int64)
    vectors[vectors==0]=1
    used=np.zeros((m//2,count),dtype=bool)
    matches=[[] for _ in range(m//2)]
    sizes=np.zeros(m//2,dtype=int)
    start=time.monotonic(); pairs=0
    # Random pair sampling supplies candidates. Every accepted pair is
    # verified with exact rational arithmetic before entering the certificate.
    while time.monotonic()-start<seconds and sizes.min()<target:
        first=rng.integers(0,count,4096)
        second=rng.integers(0,count,4096)
        for a,b in zip(first,second):
            if a==b: continue
            a=int(a);b=int(b);pairs+=1
            u,v=vectors[a],vectors[b]
            roots=-u.astype(float)/v
            order=np.argsort(roots)
            # At minus infinity the signs are -sign(v).
            code=sum(1<<j for j in range(k) if v[j]<0)
            for step in range(k+1):
                canonical=min(code,code^mask)
                if sizes[canonical]<target and not used[canonical,a] and not used[canonical,b]:
                    if step==0:
                        lam=Fraction(-int(u[order[0]]),int(v[order[0]]))-1
                    elif step==k:
                        lam=Fraction(-int(u[order[-1]]),int(v[order[-1]]))+1
                    else:
                        lam=(Fraction(-int(u[order[step-1]]),int(v[order[step-1]]))+
                             Fraction(-int(u[order[step]]),int(v[order[step]])))/2
                    vals=[Fraction(int(u[j]))+lam*int(v[j]) for j in range(k)]
                    if all(vals):
                        exact=sum(1<<j for j in range(k) if vals[j]>0)
                        if exact==code:
                            orientation=1 if code==canonical else -1
                            matches[canonical].append([a,b,lam.numerator,lam.denominator,orientation])
                            used[canonical,a]=used[canonical,b]=True
                            sizes[canonical]+=1
                if step<k:
                    code^=1<<int(order[step])
        print(json.dumps({'k':k,'seed':seed,'seconds':time.monotonic()-start,
            'pairs':pairs,'min_matching':int(sizes.min()),
            'mean_matching':float(sizes.mean()),'target':target}),flush=True)
    result={'k':k,'seed':seed,'dictionary_size':count,'target_matching':target,
            'minimum_matching':int(sizes.min()),'seconds':time.monotonic()-start,
            'scope':'Finite vector dictionary only; no universal head bound.'}
    if sizes.min()>=target:
        path=out/f'pair-matching-k{k}-seed{seed}.json'
        path.write_text(json.dumps({'vectors':vectors.tolist(),'matchings':matches,
            'target':target,'result':result})+'\n')
        result['certificate']=str(path)
    (out/f'result-k{k}-seed{seed}.json').write_text(json.dumps(result)+'\n')
    print(json.dumps(result),flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=18000)
    p.add_argument('--case-seconds',type=float,default=1800)
    p.add_argument('--multiple',type=int,default=8)
    a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    start=time.monotonic()
    for k in range(3,11):
        left=a.seconds-(time.monotonic()-start)
        if left<=0:break
        run(k,a.multiple,240000+k,min(left,a.case_seconds),a.out)


if __name__=='__main__':main()
