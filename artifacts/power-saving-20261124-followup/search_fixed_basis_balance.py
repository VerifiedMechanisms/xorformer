#!/usr/bin/env python3
"""Floating search for feasible-basis branches without balanced representatives.

This is exploratory LP evidence only. Run under `heavy`.
"""
import argparse
import json
import time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

p=argparse.ArgumentParser()
p.add_argument("--n",type=int,default=8)
p.add_argument("--seconds",type=int,default=300)
p.add_argument("--output",type=Path,required=True)
a=p.parse_args()
rng=np.random.default_rng(839352)
n=a.n;d=n+1;N=2**n
X=np.array([[1]+[(x>>(n-1-i))&1 for i in range(n)] for x in range(N)],float)
start=time.monotonic();trials=0;charts=0;best=1.;records=[]
while time.monotonic()-start<a.seconds:
    trials+=1
    w=rng.normal(size=d)*np.exp(rng.normal(size=d))
    w[0]=-w[1:].sum()/2+rng.normal()
    f=np.where(X@w>0,1.,-1.)
    b=rng.dirichlet(np.full(d, .4))
    obj=(f[:,None]*X).sum(axis=0)+rng.normal(size=d)*.01
    res=linprog(obj,A_ub=-f[:,None]*X,b_ub=-X@b,
                bounds=[(None,None)]*d,method="highs")
    if not res.success:continue
    active=np.flatnonzero(np.abs(f*(X@res.x)-X@b)<1e-7)
    if len(active)<d:continue
    ids=[]
    for i in active:
        if np.linalg.matrix_rank(X[ids+[i]])>len(ids):ids.append(int(i))
        if len(ids)==d:break
    if len(ids)<d:continue
    T=np.linalg.solve(X[ids],f[ids,None]*X[ids])
    U=X@T
    B=np.c_[b,rng.dirichlet(np.ones(d),size=30).T,
            rng.dirichlet(np.full(d,.15),size=30).T]
    scores=U@B;denoms=X@B
    feasible=np.all(np.abs(scores)>=denoms-1e-10,axis=0) & (B.min(axis=0)>1e-5)
    labels=np.unique(np.where(scores[:,feasible].T>0,1.,-1.),axis=0)
    for fnew in labels:
        charts+=1
        constraints=fnew[:,None]*U-X
        balance=linprog(np.r_[-1.,np.zeros(d-1)],A_ub=-constraints,
                        b_ub=np.zeros(N),A_eq=np.ones((1,d)),b_eq=[1],
                        bounds=[(0,None)]*d,method="highs")
        if not balance.success:continue
        value=float(balance.x[0])
        if value < 1e-5:continue  # Reject solver/classification boundary artifacts.
        if value < best-1e-6:
            best=value
            record={"trials":trials,"charts":charts,"seconds":time.monotonic()-start,
                    "basis":ids,"basis_labels":f[ids].tolist(),"full_labels":fnew.tolist(),
                    "max_b0":value,"witness":balance.x.tolist(),"matrix":T.tolist()}
            records.append(record)
            print(json.dumps({k:record[k] for k in ["trials","charts","seconds","basis","max_b0"]}),flush=True)
            a.output.write_text(json.dumps({"warning":"Floating LP exploration only","n":n,"records":records},indent=2)+"\n")
a.output.write_text(json.dumps({"warning":"Floating LP exploration only","n":n,
                               "trials":trials,"charts":charts,"records":records},indent=2)+"\n")
