#!/usr/bin/env python3
"""Search origin-contact full feasible H1 charts for failure of constant B.
Floating discovery only, followed by exact Sympy verification of any candidate.
Run as heavy python3 ... [n] [trials].
"""
import json,sys,time
from pathlib import Path
import numpy as np
from sympy import Matrix, Rational
n=int(sys.argv[1])if len(sys.argv)>1 else 6
trials=int(sys.argv[2])if len(sys.argv)>2 else 100000
rng=np.random.default_rng(248601+n)
X=np.array([[1]+[(i>>(n-1-j))&1 for j in range(n)]for i in range(2**n)],dtype=np.int64)
feasible=0;nonsing=0;failed=0;t0=time.time();result=None
for trial in range(trials):
    ids=np.r_[0,np.sort(rng.choice(np.arange(1,len(X)),n,replace=False))]
    V=X[ids]
    if abs(np.linalg.det(V))<0.5:continue
    nonsing+=1
    signs=np.r_[1,rng.choice([-1,1],n)]
    T=np.linalg.solve(V,signs[:,None]*V)
    bs=rng.integers(1,101,size=(128,n+1))
    aa=bs@T.T;av=aa@X.T;bv=bs@X.T
    good=np.flatnonzero(np.all(np.abs(av)>=bv-1e-7,axis=1))
    if len(good)==0:continue
    feasible+=len(good)
    aconst=T[:,0];vconst=X@aconst
    for j in good:
        if np.any(np.sign(av[j])!=np.sign(vconst))or np.min(np.abs(vconst))<1-1e-7:
            Te=Matrix(V.tolist()).inv()*Matrix((signs[:,None]*V).tolist())
            be=Matrix(bs[j].tolist());ae=Te*be;ve=Matrix(X.tolist())*ae;de=Matrix(X.tolist())*be
            ce=Matrix(X.tolist())*Te[:,0]
            if not all(abs(v)>=d for v,d in zip(ve,de)):continue
            differences=[i for i,(v,c)in enumerate(zip(ve,ce))if v*c<=0 or abs(c)<1]
            if not differences:continue
            result={'basis':ids.tolist(),'signs':signs.tolist(),'b':[str(v)for v in be],
                    'a':[str(v)for v in ae],'aconst':[str(v)for v in Te[:,0]],
                    'differences':differences,'labels':[v>0 for v in ve],
                    'constant_values':[str(v)for v in ce]};break
    if result:break
    if trial%10000==0:print(trial,feasible,flush=True)
out={'n':n,'trials':trial+1,'nonsingular':nonsing,'feasible_samples':feasible,
     'seconds':time.time()-t0,'exact_counterexample':result,
     'status':'exact rational certificate if present; absence is only finite sampling'}
path=Path(f'artifacts/power-saving-20261124-followup/origin-contact-basis-n{n}.json')
path.write_text(json.dumps(out,indent=2,default=bool)+'\n')
print(json.dumps(out,indent=2,default=bool))
