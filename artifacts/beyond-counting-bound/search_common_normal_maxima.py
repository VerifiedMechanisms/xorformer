#!/usr/bin/env python3
"""Search for two symmetry-related strict maxima using common normal LMIs.

The finite search is diagnostic. It solves stationarity equations and uses
eigenvector cuts to search a semidefinite feasibility problem. A later exact
rational certificate, not this script's success flag, is required for proof.
"""
import argparse
import json
import time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog


def data(n,a,b):
    codes=np.arange(2**n)
    X=((codes[:,None] >> np.arange(n)) & 1).astype(float)
    Y=np.concatenate([np.ones((len(X),1)),X],axis=1)
    D=1+X@b
    T=(Y@a)/D
    V=Y/D[:,None]
    Vb=X/D[:,None]
    J=np.concatenate([V,-T[:,None]*Vb],axis=1)
    dd=np.zeros((len(X),2*n+1,2*n+1))
    for x in range(len(X)):
        cross=np.outer(V[x],Vb[x])
        dd[x,:n+1,n+1:]=-cross
        dd[x,n+1:,:n+1]=-cross.T
        dd[x,n+1:,n+1:]=2*T[x]*np.outer(Vb[x],Vb[x])
    swapped=(codes & ~3) | ((codes & 1)<<1) | ((codes & 2)>>1)
    orbit_keys=[min(int(s),int(t)) for s,t in zip(codes,swapped)]
    keys=sorted(set(orbit_keys))
    O=np.array([[int(k==key) for key in keys] for k in orbit_keys],float)
    return X,T,J,dd,O,keys


def attempt(n,a,b,positive,rng):
    X,T,J,dd,O,keys=data(n,a,b)
    u,s,vh=np.linalg.svd(J,full_matrices=False)
    if s[-1] < 1e-7*s[0]: return None,'rank'
    Z=vh.T/s[None,:]
    ddw=np.einsum('ia,xij,jb->xab',Z,dd,Z)
    p=2*n+1
    base=np.eye(p)+np.einsum('x,xij->ij',T,ddw)
    coeff=np.einsum('xl,xij->lij',O,ddw)
    Aeq=J.T@O
    rhs=J.T@T
    # Scale the linear equations without changing their solution space.
    scales=np.linalg.norm(Aeq,axis=1)
    Aeq=Aeq/scales[:,None];rhs=rhs/scales
    directions=list(np.eye(p))
    directions.extend(rng.normal(size=(12,p)))
    cuts=[];limits=[]
    gap=.002
    for v in directions:
        v=v/np.linalg.norm(v)
        cuts.append(np.einsum('i,lij,j->l',v,coeff,v))
        limits.append(float(v@base@v)-gap)
    bounds=[((1e-4 if positive else -1000),1000)]*len(keys)
    for step in range(200):
        result=linprog(np.zeros(len(keys)),A_ub=np.array(cuts),b_ub=np.array(limits),
            A_eq=Aeq,b_eq=rhs,bounds=bounds,method='highs',
            options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
        if not result.success: return None,'lp_'+str(result.status)
        z=result.x
        H=base-np.einsum('l,lij->ij',z,coeff)
        eig,vec=np.linalg.eigh(H)
        if eig[0] > gap/2:
            return dict(n=n,a=a.tolist(),b=b.tolist(),positive_mu_required=positive,
                orbit_keys=keys,orbit_mu=z.tolist(),minimum_whitened_eigenvalue=float(eig[0]),
                stationarity_residual=float(np.max(np.abs(Aeq@z-rhs))),
                cutting_rounds=step,unit_table=(T/np.linalg.norm(T)).tolist(),
                status='NUMERICAL CANDIDATE ONLY',main_target_proved=False),'candidate'
        for j in np.flatnonzero(eig<gap/2):
            v=vec[:,j]
            cuts.append(np.einsum('i,lij,j->l',v,coeff,v))
            limits.append(float(v@base@v)-gap)
    return None,'cut_limit'


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--seconds',type=float,default=1200)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    rng=np.random.default_rng(202611231604)
    start=time.monotonic();trial=0;counts={}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open('w') as out:
        while time.monotonic()-start < args.seconds:
            n=4+trial%3
            a=rng.integers(1,9,n+1)
            b=rng.integers(1,9,n)
            if a[1]==a[2] and b[0]==b[1]: b[1]+=1
            positive=(trial//3)%2==0
            candidate,status=attempt(n,a,b,positive,rng)
            counts[status]=counts.get(status,0)+1
            if candidate:
                candidate.update(trial=trial,elapsed=time.monotonic()-start)
                out.write(json.dumps(candidate)+'\n');out.flush()
                print(json.dumps({'trial':trial,'n':n,'positive_mu':positive,'candidate':True,'elapsed':candidate['elapsed']}),flush=True)
                if positive: break
            elif trial%20==0:
                print(json.dumps({'trial':trial,'counts':counts,'elapsed':time.monotonic()-start}),flush=True)
            trial+=1


if __name__=='__main__': main()
