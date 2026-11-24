#!/usr/bin/env python3
"""Exploratory high-precision finite pattern count; NOT an exact certificate."""
import argparse, itertools, random, time
import numpy as np
import mpmath as mp
ap=argparse.ArgumentParser();ap.add_argument('--pools',type=int,default=3);ap.add_argument('--perms',type=int,default=200000);ap.add_argument('--seed',type=int,default=17);args=ap.parse_args()
mp.mp.dps=180;rng=random.Random(args.seed);nrng=np.random.default_rng(args.seed)
H=16;eps=mp.mpf('0.0001');eta=mp.mpf('0.001')
a=sorted([mp.cos(mp.pi*(2*k+1)/(2*H)) for k in range(H)])
q=[1+eps*x for x in a];p=[1-1/x for x in q]
w=[1/mp.fprod([p[i]-p[j] for j in range(H) if i!=j]) for i in range(H)]
xq=[1+eta*u for u in range(1-H,H,2)]
lag=[[mp.fprod([(p[h]-xq[j])/(xq[i]-xq[j]) for j in range(H) if j!=i]) for i in range(H)] for h in range(H)]
perms=np.argsort(nrng.random((args.perms,H)),axis=1)
indices={M:[[i for i in range(H) if i%(H//M)==prefix+(H//M)//2] for prefix in range((H//M)//2)] for M in (8,4,2,1)}
mask_indices={M:[np.sum(np.left_shift(1,perms[:,ix]),axis=1) for ix in ixlist] for M,ixlist in indices.items()}
subsets={M:[(S,sum(1<<h for h in S)) for S in itertools.combinations(range(H),M)] for M in (8,4,2)}
kernels={M:[[1/(1+eta*u-p[h]) for h in range(H)] for u in range(1-M,M,2)] for M in (8,4,2)}
all_patterns=set();start=time.time()
for trial in range(args.pools):
 y=[mp.mpf(rng.choice([-1,1]))*mp.mpf(10)**rng.randrange(-2,3) for _ in range(H)]
 rp=sum((v>0)<<j for j,v in enumerate(y))
 residues=[w[h]*mp.fsum(y[i]*lag[h][i] for i in range(H)) for h in range(H)]
 caches={};minratio=mp.inf
 for M in (8,4,2):
  cache=np.zeros(1<<H,dtype=np.uint64)
  for S,mask in subsets[M]:
   pat=0
   for j,k in enumerate(kernels[M]):
    terms=[residues[h]*k[h] for h in S];v=mp.fsum(terms)
    ratio=abs(v)/mp.fsum(abs(t) for t in terms);minratio=min(minratio,ratio)
    pat|=int(v>0)<<j
   cache[mask]=pat
  caches[M]=cache
 cache=np.zeros(1<<H,dtype=np.uint64)
 for h in range(H):cache[1<<h]=int(residues[h]>0)
 caches[1]=cache
 pats=np.zeros(args.perms,dtype=np.uint64);offset=0
 for M in (8,4,2,1):
  for masks in mask_indices[M]:pats |= caches[M][masks]<<np.uint64(offset);offset+=M
 distinct=set(map(int,np.unique(pats)));all_patterns.update((rp<<32)+x for x in distinct)
 print(trial,'desc',len(distinct),'total',len(all_patterns),'log2desc',np.log2(len(distinct)),'min_ratio',mp.nstr(minratio,8),'sec',round(time.time()-start,1),flush=True)
