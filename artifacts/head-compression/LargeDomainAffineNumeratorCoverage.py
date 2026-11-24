#!/usr/bin/env python3
"""Floating-point fixed-affine-numerator coverage; use heavy.

A_h(x) and all positive row directions are fixed once, independent of labels.
Only scalar column residues, offsets, and bias vary. The affine coefficient
space is enumerated by adding its homogenizing coordinate as one extra
arrangement hyperplane. These are exploratory numerics, not certificates.
"""
import argparse,itertools,json,time
import numpy as np
from LargeDomainFixedDirectionCoverage import coverage


def main():
 p=argparse.ArgumentParser()
 p.add_argument('--dimension',type=int,default=4)
 p.add_argument('--heads',type=int,default=4)
 p.add_argument('--samples',type=int,default=200)
 p.add_argument('--epsilon',type=float,default=.001)
 p.add_argument('--seed',type=int,default=2411)
 p.add_argument('--output')
 args=p.parse_args()
 rng=np.random.default_rng(args.seed)
 bits=np.array(list(itertools.product((0,1),repeat=args.dimension)))
 n=len(bits); H=args.heads
 d=1+args.epsilon*rng.uniform(-1,1,(H,args.dimension))
 a=rng.normal(size=(H,args.dimension))
 numerators=bits@a.T
 subsets=np.array(list(itertools.combinations(range(n+1),H+1)))
 signs=np.array(list(itertools.product((-1,1),repeat=H+1)))
 seen=np.zeros(1<<n,dtype=bool)
 t=time.monotonic()
 print(json.dumps({'dimension':args.dimension,'heads':H,'directions':d.tolist(),
  'fixed_row_numerators':a.tolist(),'offset_interval':[1,1.125],
  'status':'floating_point_only'}),flush=True)
 for sample in range(args.samples):
  b=1+rng.uniform(.001,.124,H)
  reciprocal=1/(bits@d.T+b)
  background=np.sum(numerators*reciprocal,axis=1)
  f=np.column_stack((np.ones(n),reciprocal,background))
  f=np.vstack((f,np.r_[np.zeros(H+1),1]))
  patterns,condition,vertices=coverage(f,subsets,signs)
  # coverage canonically sets the last (homogenizing) sign negative.
  # Complementing sets it positive, so the final coefficient is rescalable to1.
  actual=(1<<n)-1-patterns
  seen[actual]=True
  if sample<10 or sample%10==9 or seen.all():
   print(json.dumps({'sample':sample,'covered':int(seen.sum()),'total':len(seen),
    'condition':condition,'regular_vertices':vertices,'seconds':time.monotonic()-t}),flush=True)
  if seen.all(): break
 report={'covered':int(seen.sum()),'total':len(seen),'missing':np.where(~seen)[0].tolist(),
  'directions':d.tolist(),'fixed_row_numerators':a.tolist(),'args':vars(args),
  'seconds':time.monotonic()-t}
 if args.output:
  with open(args.output,'w') as f: json.dump(report,f)
 print(json.dumps({'final_covered':report['covered'],'total':len(seen),
  'first_missing':report['missing'][:32],'seconds':report['seconds']}),flush=True)

if __name__=='__main__':main()
