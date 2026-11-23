#!/usr/bin/env python3
"""Diagnostic search for multiple maxima of a normalized one-head height.

No optimizer output is a proof. Interior candidates are independently checked
against the analytic gradient and Hessian, then saved for possible interval
certification. Failure to find a candidate says nothing about nonexistence.
"""
import argparse
import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import minimize


def profile(b, X, mu, hessian=False):
    D = 1 + X @ b
    V = X / D[:, None]
    G, K = V.T @ V, V.T @ mu
    r = np.linalg.solve(G, K)
    T = V @ r
    R = mu - T
    value = K @ r
    gradient = -2 * X.T @ (R*T/D)
    if not hessian:
        return value, gradient
    Q = V.T @ (((2*T-mu)/D)[:, None]*X)
    second = 2*Q.T @ np.linalg.solve(G,Q)
    second += X.T @ (((4*R*T-2*T*T)/(D*D))[:, None]*X)
    return value, gradient, second, T/np.sqrt(value)


def derivative_check():
    rng = np.random.default_rng(19)
    for n in [3,4,5]:
        X = ((np.arange(1,2**n)[:,None] >> np.arange(n)) & 1).astype(float)
        b, mu = rng.uniform(.3,2,n), rng.normal(size=len(X))
        value, gradient, second, _ = profile(b,X,mu,True)
        h = 1e-5
        eye = np.eye(n)
        for j in range(n):
            vp,gp=profile(b+h*eye[j],X,mu)
            vm,gm=profile(b-h*eye[j],X,mu)
            assert abs((vp-vm)/(2*h)-gradient[j]) < 1e-6
            assert np.max(np.abs((gp-gm)/(2*h)-second[:,j])) < 1e-5
        assert abs(second-second.T).max() < 1e-10


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--seconds',type=float,default=1800)
    parser.add_argument('--starts',type=int,default=64)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    derivative_check()
    rng=np.random.default_rng(202611231558)
    start=time.monotonic()
    trial=0
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open('w') as out:
        while time.monotonic()-start < args.seconds:
            n=3+trial%5
            X=((np.arange(1,2**n)[:,None] >> np.arange(n)) & 1).astype(float)
            mode=(trial//5)%4
            if mode==0:
                mu=rng.choice([-1,1],len(X))
            elif mode==1:
                mu=rng.integers(-20,21,len(X))
            elif mode==2:
                mu=rng.integers(1,21,len(X))
            else:
                mu=np.zeros(len(X),dtype=int)
                for j in rng.choice(len(X),min(n+1,len(X)),replace=False):
                    mu[j]=rng.integers(1,21)
            muscale=np.linalg.norm(mu)
            mus=mu/muscale
            candidates=[]
            boundary=0
            rejected=0
            for attempt in range(args.starts):
                if time.monotonic()-start >= args.seconds:
                    break
                theta0=rng.uniform(-6,6,n) if attempt else np.zeros(n)
                def fun(theta):
                    b=np.exp(theta)
                    value,gradient=profile(b,X,mus)
                    return -value,-b*gradient
                result=minimize(fun,theta0,jac=True,method='L-BFGS-B',
                    bounds=[(-12,12)]*n,
                    options={'maxiter':1000,'gtol':1e-11,'ftol':1e-15,'maxls':40})
                if np.max(np.abs(result.x)) > 11.9:
                    boundary+=1
                    continue
                b=np.exp(result.x)
                value,g,H,T=profile(b,X,mus,True)
                gradient=b*g
                Hessian=b[:,None]*H*b[None,:]+np.diag(gradient)
                eig=np.linalg.eigvalsh(Hessian)
                if np.max(np.abs(gradient)) > 1e-7 or eig[-1] >= -1e-8:
                    rejected+=1
                    continue
                if any(np.linalg.norm(T-np.array(c['unit_table'])) < 1e-4 for c in candidates):
                    continue
                candidates.append(dict(b=b.tolist(),value=float(value),
                    gradient_max=float(np.max(np.abs(gradient))),
                    hessian_eigenvalues=eig.tolist(),unit_table=T.tolist(),
                    sign_compatible=bool(np.all(mu*T>=0)),
                    optimizer_success=bool(result.success)))
            record=dict(trial=trial,n=n,mode=mode,integer_mu=mu.tolist(),
                numerical_candidates=candidates,boundary_runs=boundary,
                rejected_interior_runs=rejected,elapsed=time.monotonic()-start,
                status='NUMERICAL ONLY; not an interval or Lean certificate',
                main_target_proved=False)
            out.write(json.dumps(record)+'\n');out.flush()
            print(json.dumps({k:v for k,v in record.items() if k not in ['integer_mu','numerical_candidates']} | {'candidates':len(candidates)}),flush=True)
            trial+=1


if __name__=='__main__':
    main()
