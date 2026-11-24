#!/usr/bin/env python3
"""Generate exact biased Haar samples; run through `heavy`.

Requires pplpy, whose MIP_Problem is an ordinary rational LP until integer
variables are explicitly declared. This script declares none. Output is
compatible with butterfly-adaptive-haar-sample-check.py. Tested targets
are only a finite sample; solver success is not a universality claim.
"""
import argparse
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import json
import math
import random
import time
import sys
import ppl
sys.set_int_max_str_digits(0)

parser=argparse.ArgumentParser();parser.add_argument('--dimension',type=int,default=5)
parser.add_argument('--skip',type=int,default=0);parser.add_argument('--count',type=int,default=10);parser.add_argument('--seed',type=int,default=333)
parser.add_argument('--epsilon',default='1/100');parser.add_argument('--root-alternating',action='store_true')
parser.add_argument('--upper-half',action='store_true');parser.add_argument('--output',required=True)
args=parser.parse_args();d=args.dimension;H=1<<d;epsilon=F(args.epsilon);powers=[2**j for j in range(d)]
spec=importlib.util.spec_from_file_location('bf',Path(__file__).with_name('butterfly-rectangle-decoder-check.py'))
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)
sw=bf.switches(d);blocks=list(dict.fromkeys((k,g) for k,s,g in sw))
p=[sum((epsilon**powers[j] for j in range(d) if y&(1<<j)),F(0)) for y in range(H)]
rng=random.Random(args.seed);start=time.time();witnesses=[];infeasible=[]
for ix in range(args.count):
    bits=[((s>>(k-1))&1) if args.root_alternating and k==d-1 else rng.randrange(2)
          for k,s,g in sw]
    if ix<args.skip:continue
    pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)];rows=[]
    for k,g in blocks:
        pos=[s for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==0]
        neg=[s for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==1]
        for a in pos:
            for b in neg:
                sign=1 if p[a]>p[b] else -1
                rows.append([F(sign*(0 if inv[y]>>(k+1)!=g else
                      1 if not inv[y]&(1<<k) else -1))/((1-p[a]-p[y])*(1-p[b]-p[y]))
                      for y in range(H)])
    variables=[ppl.Variable(j) for j in range(H)];constraints=ppl.Constraint_System()
    for row in rows:
        denominator=math.lcm(*(v.denominator for v in row))
        constraints.insert(ppl.Linear_Expression([int(v*denominator) for v in row],0)>=denominator)
    if args.upper_half:
        for j in range(H//2):constraints.insert(variables[j]==0)
    program=ppl.MIP_Problem(H,constraints,ppl.Linear_Expression(0))
    feasible=program.is_satisfiable()
    if feasible:
        point=program.optimizing_point()
        c=[F(int(point.coefficient(v)),int(point.divisor())) for v in variables]
        assert all(sum(a*b for a,b in zip(row,c))>=1 for row in rows)
        witnesses.append(dict(bits=bits,c=list(map(str,c))))
    else:infeasible.append(bits)
    data=dict(dimension=d,epsilon=str(epsilon),powers=powers,witnesses=witnesses,
              infeasible=infeasible,root_alternating=args.root_alternating,upper_half=args.upper_half)
    Path(args.output).write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(dict(index=ix,feasible=feasible,seconds=time.time()-start)),flush=True)
