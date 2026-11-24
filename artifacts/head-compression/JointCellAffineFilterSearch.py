#!/usr/bin/env python3
"""Exploratory Wronskians of affine-numerator Boolean filters, not certificates.

Rows use reciprocal derivatives with their nonzero row constants omitted.
All evaluation points lie beyond the largest pole. No observed constant sign
is claimed to establish a zero bound or a Chebyshev property.
"""
import mpmath as mp, random, json, argparse
p=argparse.ArgumentParser();p.add_argument('--c',type=int,default=6);p.add_argument('--trials',type=int,default=20);p.add_argument('--seed',type=int,default=810)
p.add_argument('--dps',type=int,default=140);p.add_argument('--near-equal',action='store_true');a=p.parse_args()
mp.mp.dps=a.dps
rng=random.Random(a.seed)
def wronskian(w,d):
 c=len(w); N=1<<c
 poles=[sum(w[i] for i in range(c) if m>>i&1) for m in range(N)]
 R=[[((-1)**(c-m.bit_count()))*(1 if j==0 else ((m>>(j-1))&1)) for m in range(N)] for j in range(c+1)]
 mat=mp.matrix(c+1)
 for k in range(c+1):
  den=[(d-s)**(-k-1) for s in poles]
  for j in range(c+1):mat[k,j]=mp.fsum(R[j][m]*den[m] for m in range(N))
 # no alternating row factors; irrelevant to sign reversals
 for k in range(c+1):
  sc=max(abs(mat[k,j]) for j in range(c+1))
  for j in range(c+1):mat[k,j]/=sc
 return mp.det(mat)
for trial in range(a.trials):
 w=([1+mp.mpf(i)/1000 for i in range(a.c)] if a.near_equal else
    [mp.mpf(rng.randrange(1,10000)) for i in range(a.c)])
 w.sort(); W=sum(w)
 vals=[]
 grid=(['1.00001','1.001','1.01','1.03','1.1','1.3','1.5','2','5','10','100']
       if a.near_equal else ['1.00001','1.001','1.01','1.1','1.5','2','5','10','100'])
 for ratio in grid:
  det=wronskian(w,W*mp.mpf(ratio));vals.append(int(mp.sign(det)))
 print(json.dumps({'status':'finite floating-point exploration only','trial':trial,
     'c':a.c,'dps':a.dps,'weights':[str(x) for x in w],
     'distance_ratios':grid,'signs':vals}),flush=True)
