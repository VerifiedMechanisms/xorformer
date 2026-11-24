"""Search larger mixed tribes on an exact symmetry quotient.

Each of the three terms requires m specified ones and m specified zeros.
The fitted vanilla parameters are constant within each of the six groups,
so full count-grid verification implies full Boolean-cube verification.
"""
import argparse
import itertools
import json
from pathlib import Path
import numpy as np
from search_mixed_tribes import fit


def data(m):
    counts=np.array(list(itertools.product(range(m+1),repeat=6)),dtype=int)
    target=np.any((counts[:,::2]==m)&(counts[:,1::2]==0),axis=1)
    return (2*counts-m)/m,np.where(target,1.,-1.)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--m',type=int,default=3)
    ap.add_argument('--restarts',type=int,default=12)
    ap.add_argument('--maxiter',type=int,default=10000)
    ap.add_argument('--seed',type=int,default=606061)
    ap.add_argument('--out',default='/tmp/mixed_tribes_grid.jsonl')
    ap.add_argument('--initial')
    args=ap.parse_args();z,y=data(args.m)
    initial=None
    if args.initial:
        initial=json.loads(Path(args.initial).read_text().splitlines()[-1])
    for record in fit(z,y,args.restarts,args.seed,args.maxiter,initial):
        record['m']=args.m
        with Path(args.out).open('a') as f:f.write(json.dumps(record)+'\n')
        print({k:v for k,v in record.items() if k not in ['beta','numerators']},flush=True)


if __name__=='__main__':main()
