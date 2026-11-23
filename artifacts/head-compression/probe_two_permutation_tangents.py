#!/usr/bin/env python3
"""Explore two nonconstant permutation lists, without claiming feasibility.

Ranks are computed over one finite field. They are diagnostics only.
No conclusion about real signs, arbitrary dimensions, or worst-case
head complexity follows from a large rank in this finite experiment.
Run through heavy. Requires python-flint.
"""
import argparse
import json
import math
import random
import time
from pathlib import Path
from flint import nmod_mat


def roots(x):
    n=len(x)
    return [sum(x)]+[k*(1-x[k-1])+sum(x[k:]) for k in range(1,n+1)]


def evaluate(n, permutation, mask, prime):
    m=n+1
    variables=2*m*m
    d=[((-1)**j*math.factorial(j)*math.factorial(n-j)) % prime
       for j in range(m)]
    c,r=[],[]
    for value in range(1 << n):
        x=[(value >> i) & 1 for i in range(n)]
        y=[x[permutation[i]] ^ ((mask >> i) & 1) for i in range(n)]
        u,v=roots(x),roots(y)
        inv_u=[u.index(j) for j in range(m)]
        inv_v=[v.index(j) for j in range(m)]
        z=[1]+x
        rows=[]
        for j in range(m):
            row=[0]*variables
            for i,bit in enumerate(z):
                row[m*inv_u[j]+i]=d[j]*bit % prime
                row[m*m+m*inv_v[j]+i]=-d[j]*bit % prime
            rows.append(row)
        r.append(rows[0])
        c.extend([[(a-b) % prime for a,b in zip(rows[j],rows[0])]
                  for j in range(1,m)])
    rank_c=nmod_mat(c,prime).rank()
    rank_cr=nmod_mat(c+r,prime).rank()
    return dict(constraint_rank=rank_c,combined_rank=rank_cr,
                output_dimension=rank_cr-rank_c)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--min-n',type=int,default=4)
    parser.add_argument('--max-n',type=int,default=10)
    parser.add_argument('--trials',type=int,default=128)
    parser.add_argument('--seconds',type=float,default=14400)
    parser.add_argument('--prime',type=int,default=2147483647)
    parser.add_argument('--seed',type=int,default=2026112312)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    rng=random.Random(args.seed)
    started=time.monotonic()
    events=[]
    for n in range(args.min_n,args.max_n+1):
        seen=set()
        for trial in range(args.trials):
            if time.monotonic()-started > args.seconds or (args.out/'STOP').exists():
                break
            if trial==0:
                permutation=list(range(n));mask=(1 << n)-1
            else:
                while True:
                    permutation=rng.sample(list(range(n)),n)
                    mask=rng.randrange(1 << n)
                    if (tuple(permutation),mask) not in seen: break
            seen.add((tuple(permutation),mask))
            event=dict(n=n,trial=trial,permutation=permutation,complement_mask=mask)
            event.update(evaluate(n,permutation,mask,args.prime))
            event['elapsed_seconds']=time.monotonic()-started
            events.append(event)
            with (args.out/'events.jsonl').open('a') as stream:
                stream.write(json.dumps(event)+'\n')
            print(json.dumps(event),flush=True)
        if time.monotonic()-started > args.seconds or (args.out/'STOP').exists(): break
    maxima={n:max(e['output_dimension'] for e in events if e['n']==n)
            for n in sorted({e['n'] for e in events})}
    result=dict(prime=args.prime,seed=args.seed,trials=len(events),
        seconds=time.monotonic()-started,maxima=maxima,
        scope='Finite-field tangent ranks for specified pairs only. No real sign or universal head theorem.')
    (args.out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__=='__main__': main()
