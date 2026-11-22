"""Active-set variable projection for full-cube sign representations.

The convex readout problem is solved inside each denominator update. A result
is a theorem only when the separate exact rational verifier accepts it.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
import numpy as np
from scipy.linalg import cho_factor, cho_solve
from scipy.optimize import minimize
from search_representations import cube, labels, exact_certificate


def inner_solution(features,y,sigma,ridge,warm=None,tol=1e-9):
    p=features.shape[1]
    u=np.zeros(p) if warm is None else warm.copy()
    for iteration in range(100):
        score=sigma+features@u
        active=y*score<1
        residual=np.where(active,score-y,0)
        value=residual@residual+ridge*(u@u)
        gradient=features.T@residual+ridge*u
        if np.linalg.norm(gradient,np.inf)<tol:return u,iteration,True
        a=features[active]
        gram=a.T@a
        gram.flat[::p+1]+=ridge
        delta=cho_solve(cho_factor(gram,lower=True,check_finite=False),gradient,check_finite=False)
        descent=gradient@delta
        step=1.0
        for _ in range(40):
            candidate=u-step*delta
            candidate_residual=np.maximum(0,1-y*(sigma+features@candidate))
            candidate_value=candidate_residual@candidate_residual+ridge*(candidate@candidate)
            if candidate_value<=value-1e-4*step*descent:break
            step*=.5
        u=candidate
        if step*np.linalg.norm(delta)<1e-12*(1+np.linalg.norm(u)):
            return u,iteration,False
    return u,100,False


def objective(theta,x,y,orientation,sigma,ridge,state=None):
    n,h=x.shape[1],len(orientation)
    w=np.exp(theta.reshape(n,h))
    d=1+x@(w*(1-2*orientation))+w.sum(axis=0)*orientation
    features=(x[:,:,None]/d[:,None,:]).reshape(len(x),n*h)
    warm=state.get('u') if state is not None else None
    u,iterations,converged=inner_solution(features,y,sigma,ridge,warm)
    a=x@u.reshape(n,h);score=sigma+np.sum(a/d,axis=1)
    residual=np.where(y*score<1,score-y,0)
    value=(residual@residual+ridge*(u@u))/len(x)
    gd=-2*residual[:,None]*a/(len(x)*d*d)
    gw=(x.T@gd)*(1-2*orientation)+gd.sum(axis=0)*orientation
    if state is not None:
        state.update(u=u,weights=w,margin=float(np.min(y*score)),value=float(value),
                     inner_iterations=iterations,inner_converged=converged,theta=theta.copy())
    return value,(gw*w).ravel()


def gradient_check():
    x=cube(3);y=labels(x,'random',192);o=np.array([0.,1.]);sigma=int(y[0])
    theta=np.random.default_rng(12).normal(size=6);ridge=.01
    _,grad=objective(theta,x,y,o,sigma,ridge)
    errors=[]
    for i in range(len(theta)):
        delta=np.zeros_like(theta);delta[i]=1e-5
        numeric=(objective(theta+delta,x,y,o,sigma,ridge)[0]-
                 objective(theta-delta,x,y,o,sigma,ridge)[0])/2e-5
        errors.append(abs(numeric-grad[i]))
    assert max(errors)<1e-7,errors
    return max(errors)


def fit(n,h,restart,iterations,deadline):
    seed=271828;started=time.monotonic();x=cube(n);y=labels(x,'random',seed)
    sigma=int(y[0]);o=(np.arange(h)%2).astype(float)
    theta=np.random.default_rng(seed+100003*restart+7919*h).uniform(-5,5,n*h)
    state={};stages=[];count=0
    class Found(Exception):pass
    class Timeout(Exception):pass
    for ridge in [1e-5,1e-8,1e-11]:
        def evaluate(t):
            if time.monotonic()>deadline:raise Timeout
            result=objective(t,x,y,o,sigma,ridge,state)
            if state['margin']>1e-6:raise Found
            return result
        def callback(t):
            nonlocal count
            count+=1
            if count%50==0:
                print(json.dumps(dict(event='iteration',n=n,heads=h,restart=restart,
                    iteration=count,ridge=ridge,loss=state['value'],margin=state['margin'],
                    inner_converged=state['inner_converged'],elapsed=time.monotonic()-started)),flush=True)
        try:
            result=minimize(evaluate,theta,jac=True,method='L-BFGS-B',
                bounds=[(-12,12)]*len(theta),callback=callback,
                options=dict(maxiter=iterations,ftol=1e-13,gtol=1e-9,maxls=30,maxcor=20))
            theta=result.x;stages.append(dict(ridge=ridge,message=str(result.message)))
        except Found:
            stages.append(dict(ridge=ridge,message='positive floating margins'));break
        except Timeout:
            stages.append(dict(ridge=ridge,message='global deadline'));break
        except np.linalg.LinAlgError:
            stages.append(dict(ridge=ridge,message='floating Cholesky failed'));break
    cert=None
    if state.get('margin',-1)>0:
        cert=exact_certificate(x,y,state['u'].reshape(n,h),state['weights'],o,sigma,bits=40)
    record=dict(n=n,heads=h,family='random',seed=seed,restart=restart,
        iterations=count,stages=stages,elapsed_seconds=time.monotonic()-started,
        floating_min_margin=state.get('margin'),loss=state.get('value'),
        status='CERTIFIED_REPRESENTATION' if cert else 'UNKNOWN',
        label_sha256=hashlib.sha256(y.astype(np.int8).tobytes()).hexdigest())
    return record,cert


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=7200);p.add_argument('--iterations',type=int,default=1500)
    p.add_argument('--restarts',type=int,default=3);p.add_argument('--check-only',action='store_true')
    a=p.parse_args();print(json.dumps(dict(event='gradient_check',error=gradient_check())),flush=True)
    if a.check_only:return
    a.output.mkdir(parents=True,exist_ok=True);deadline=time.monotonic()+a.seconds
    with (a.output/'results.jsonl').open('a',buffering=1) as log:
        for n,counts in [(8,[4,6,8,10,12]),(9,[7,10,14,18]),(10,[10,16,24,32])]:
            for h in counts:
                for restart in range(a.restarts):
                    record,cert=fit(n,h,restart,a.iterations,deadline)
                    if cert:
                        name=f'n{n}-h{h}-projected-hinge-r{restart}.json'
                        (a.output/name).write_text(json.dumps(cert)+'\n');record['certificate']=name
                    line=json.dumps(record);log.write(line+'\n');print(line,flush=True)
                    if cert:break
                    if time.monotonic()>deadline:return

if __name__=='__main__':main()
