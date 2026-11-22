"""Variable-projection adversary for proposed hard Boolean functions.

Only successful exact rational certificates are conclusions. Numerical failure
has status UNKNOWN, never a lower bound. Sustained runs must use `heavy`.
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


def objective(theta, x, target, orientation, ridge, keep=None):
    n, h = x.shape[1], len(orientation)
    w = np.exp(theta.reshape(n, h))
    d = 1 + x @ (w * (1 - 2*orientation)) + w.sum(axis=0)*orientation
    features = (x[:, :, None]/d[:, None, :]).reshape(len(x), n*h)
    gram = features.T @ features
    gram.flat[::len(gram)+1] += ridge
    u = cho_solve(cho_factor(gram, lower=True, check_finite=False),
                  features.T @ target, check_finite=False).reshape(n, h)
    a = x @ u
    residual = np.sum(a/d, axis=1)-target
    value = (residual @ residual + ridge*np.sum(u*u))/len(x)
    gd = -2*residual[:, None]*a/(len(x)*d*d)
    gw = (x.T @ gd)*(1-2*orientation) + gd.sum(axis=0)*orientation
    gradient = (gw*w).ravel()
    if keep is not None:
        keep.update(u=u, weights=w, residual=residual, value=value)
    return value, gradient


def check_gradient():
    x=cube(3); o=np.array([0.,1.]); target=labels(x,'random',912)-1
    t=np.random.default_rng(1).normal(size=6); ridge=.01
    _,g=objective(t,x,target,o,ridge)
    errors=[]
    for i in range(len(t)):
        step=np.zeros_like(t); step[i]=1e-5
        numeric=(objective(t+step,x,target,o,ridge)[0]-
                 objective(t-step,x,target,o,ridge)[0])/2e-5
        errors.append(abs(g[i]-numeric))
    assert max(errors)<1e-7,errors
    return max(errors)


def fit(n,h,seed,restart,iterations,deadline):
    started=time.monotonic(); x=cube(n); y=labels(x,'random',seed)
    sigma=int(y[0]); target=y-sigma
    rng=np.random.default_rng(seed+100003*restart+7919*h)
    orientation=(np.arange(h)%2).astype(float)
    theta=rng.uniform(-5,5,size=n*h)
    state={}; total_iterations=0
    class Found(Exception): pass
    class Timeout(Exception): pass
    stages=[]
    for ridge in [1e-5,1e-8,1e-11]:
        stage_iterations=0
        def evaluate(t):
            if time.monotonic()>deadline: raise Timeout
            result=objective(t,x,target,orientation,ridge,state)
            state['theta']=t.copy()
            score=state['residual']+y
            state['margin']=float(np.min(y*score))
            if state['margin']>1e-6: raise Found
            return result
        def callback(t):
            nonlocal total_iterations,stage_iterations
            total_iterations+=1; stage_iterations+=1
            if stage_iterations%100==0:
                print(json.dumps(dict(event='iteration',n=n,heads=h,restart=restart,
                    ridge=ridge,iterations=total_iterations,loss=state['value'],
                    margin=state['margin'],elapsed=time.monotonic()-started)),flush=True)
        try:
            result=minimize(evaluate,theta,jac=True,method='L-BFGS-B',
                bounds=[(-12,12)]*len(theta),callback=callback,
                options=dict(maxiter=iterations,ftol=1e-13,gtol=1e-9,maxls=40,maxcor=30))
            theta=result.x
            stages.append(dict(ridge=ridge,iterations=stage_iterations,message=str(result.message)))
        except Found:
            stages.append(dict(ridge=ridge,message='positive floating margins'))
            break
        except Timeout:
            stages.append(dict(ridge=ridge,message='global time limit'))
            break
        except np.linalg.LinAlgError:
            stages.append(dict(ridge=ridge,message='floating Cholesky failed'))
            break
    cert=None
    if state.get('margin',-1)>0:
        cert=exact_certificate(x,y,state['u'],state['weights'],orientation,sigma,bits=40)
    record=dict(n=n,heads=h,family='random',seed=seed,restart=restart,
        iterations=total_iterations,stages=stages,elapsed_seconds=time.monotonic()-started,
        floating_min_margin=state.get('margin'),loss=state.get('value'),
        status='CERTIFIED_REPRESENTATION' if cert else 'UNKNOWN',
        label_sha256=hashlib.sha256(y.astype(np.int8).tobytes()).hexdigest())
    return record,cert


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=7200)
    p.add_argument('--iterations',type=int,default=1000)
    p.add_argument('--restarts',type=int,default=3)
    p.add_argument('--check-only',action='store_true');a=p.parse_args()
    print(json.dumps(dict(event='gradient_check',max_error=check_gradient())),flush=True)
    if a.check_only:return
    a.output.mkdir(parents=True,exist_ok=True);deadline=time.monotonic()+a.seconds
    with (a.output/'results.jsonl').open('a',buffering=1) as log:
        for n,counts in [(8,[4,6,8,10,12]),(9,[7,10,14,18]),(10,[10,16,24,32])]:
            for h in counts:
                for restart in range(a.restarts):
                    record,cert=fit(n,h,271828,restart,a.iterations,deadline)
                    if cert:
                        name=f'n{n}-h{h}-varproj-r{restart}.json'
                        (a.output/name).write_text(json.dumps(cert)+'\n');record['certificate']=name
                    line=json.dumps(record);log.write(line+'\n');print(line,flush=True)
                    if cert:break
                    if time.monotonic()>deadline:return

if __name__=='__main__':main()
