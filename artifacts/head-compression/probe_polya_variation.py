#!/usr/bin/env python3
"""Finite Pólya-base diagnostic. Run through heavy; no universal claim."""
from fractions import Fraction as F
import itertools,json,random,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from search_weighted_reciprocal_variation import compile_weighted
from verify_certificate import verify
n=6; points=list(itertools.product((0,1),repeat=n)); rng=random.Random(2026112315)
labels=[rng.choice((-1,1)) for _ in points]; Z=np.array([[1]+list(x) for x in points],dtype=float)
started=time.monotonic(); records=[]
for trial in range(100):
 b=([1]*n if trial==0 else [rng.randrange(1,13) for _ in range(n)])
 base=[1]+b; rows=[base,[2]+b]+[[1]+[t+(i==j) for j,t in enumerate(b)] for i in range(n)]
 weights=[1+sum(b),-2]+[-t for t in b]
 den=Z@np.array(rows,dtype=float).T
 features=np.concatenate([np.ones((len(points),1))]+[Z/den[:,h:h+1]**2 for h in range(n+2)],axis=1)
 result=linprog(np.zeros(features.shape[1]),A_ub=-np.array(labels)[:,None]*features,b_ub=-2*np.ones(len(points)),bounds=(None,None),method='highs')
 records.append({'trial':trial,'b':b,'status':int(result.status)})
 if result.success:
  theta=[F(float(t)).limit_denominator(10**9) for t in result.x]
  directions=[theta[1+h*(n+1):1+(h+1)*(n+1)] for h in range(n+2)]
  try:c=compile_weighted(rows,weights,directions,theta[0],labels)
  except AssertionError:
   records[-1]['rounding_failed']=True; continue
  path=Path('/out/head-compression/polya-variation-random-n6-h8.json');path.write_text(json.dumps(c)+'\n')
  audit=verify(path)
  records[-1].update(certificate=str(path),audit=audit)
  print(json.dumps(records[-1]),flush=True);break
out={'records':records,'seconds':time.monotonic()-started,'target_proved':False}
Path('/out/head-compression/polya-variation-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'trials':len(records),'last_status':records[-1]['status'],'seconds':out['seconds']}),flush=True)
