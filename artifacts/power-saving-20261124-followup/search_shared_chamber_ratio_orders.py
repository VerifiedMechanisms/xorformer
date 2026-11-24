#!/usr/bin/env python3
"""Explore whether coefficient ratio order fixes a full-feasible H1 chart.
Numerical search only; candidate outputs contain exact rational input vectors.
"""
import json
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from sympy import Matrix
rng=np.random.default_rng(2481);n=6;d=7
X=np.array([[1]+[(i>>(n-1-j))&1 for j in range(n)]for i in range(2**n)],dtype=int)
ids=[7,8,13,17,19,32,43];signs=np.array([1,1,1,1,-1,1,-1])
T=Matrix(X[ids].tolist()).inv()*Matrix((signs[:,None]*X[ids]).tolist())
Tf=np.array(T,dtype=float)
asrc=[np.array([11,-9,-18,-9,-9,-9,11]),np.array([15,-13,-28,-13,-17,-13,19])]
labels=[np.where(X@a>0,1,-1)for a in asrc]
vertices=[]
for branch in range(2):
    V=[]
    for k in range(300):
        lp=linprog(rng.normal(size=d),A_ub=X-labels[branch][:,None]*(X@Tf),b_ub=np.zeros(len(X)),
                   A_eq=np.ones((1,d)),b_eq=[1.],bounds=[(1e-4,None)]*d,method='highs')
        if lp.success:V.append(lp.x)
    vertices.append(np.array(V))
seen=[{},{}];match=None
for k in range(100000):
    branch=k%2;V=vertices[branch]
    ix=rng.integers(len(V),size=5);ww=rng.dirichlet(np.ones(5));b=ww@V[ix]
    a=Tf@b;rat=a/b
    if min(np.diff(np.sort(rat)))<1e-6:continue
    order=tuple(np.argsort(rat).tolist())
    seen[branch].setdefault(order,b)
    if order in seen[1-branch]:
        match=(order,[seen[0][order],seen[1][order]]);break
out={'status':'floating exploratory, no proof','orders_seen':[len(v)for v in seen],
     'basis':ids,'signs':signs.tolist(),'T':[[str(v)for v in row]for row in T.tolist()]}
if match:
    out['common_order']=match[0];out['b']=[b.tolist()for b in match[1]]
    out['a']=[(Tf@b).tolist()for b in match[1]]
# Exact integer search following the floating candidate. All tests below use
# integer matrix products; final ratio comparisons use Fraction.
Ti=np.array(T,dtype=np.int64)
exact_seen={}; exact=None
for batch in range(100):
    bs=rng.integers(1,31,size=(10000,d),dtype=np.int64)
    aa=bs@Ti.T
    vv=aa@X.T; bb=bs@X.T
    good=np.flatnonzero(np.all(np.abs(vv)>=bb,axis=1))
    for j in good:
        ratios=[Fraction(int(aa[j,i]),int(bs[j,i]))for i in range(d)]
        if len(set(ratios))<d:continue
        order=tuple(sorted(range(d),key=lambda i:ratios[i]))
        label=tuple((vv[j]>0).tolist())
        row={'b':bs[j].tolist(),'a':aa[j].tolist(),'labels':list(label)}
        if order in exact_seen and exact_seen[order]['labels']!=list(label):
            exact=(order,[exact_seen[order],row]);break
        exact_seen.setdefault(order,row)
    if exact:break
if exact:
    out['exact_common_order']=exact[0];out['exact_pair']=exact[1]
    out['status']='floating exploration followed by exact integer candidate checks; Lean certificate separate'
Path('artifacts/power-saving-20261124-followup/shared-chamber-ratio-order-search.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
