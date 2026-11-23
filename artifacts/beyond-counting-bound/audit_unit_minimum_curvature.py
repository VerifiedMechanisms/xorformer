"""Replay one full-cube optimization trial and audit numerical KKT curvature.

This is an exploratory diagnostic. In particular small residuals and floating
eigenvalues are not certificates of stationarity or local minimality.
"""
import argparse
import json
from pathlib import Path
import time
import numpy as np
from scipy.linalg import null_space
from scipy.optimize import minimize, nnls
from search_full_cube_unit_minima import mixed_score_jac


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--trial',type=int,default=495)
    p.add_argument('--refinements',type=int,default=0)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();rng=np.random.default_rng(119084);start=time.monotonic()
    for trial in range(a.trial+1):
        n,h=[(6,3),(7,3),(7,4),(8,4)][trial%4]
        orientation=rng.choice([-1.,1.],size=h)
        u=rng.normal(size=(n,h));logp=rng.uniform(-2,2,size=(n,h))
        if trial%3==0:
            u-=u.mean(axis=1,keepdims=True)
            logp=rng.uniform(-1,1,size=(n,1))+rng.normal(scale=.5,size=(n,h))
    k=n*h;sample=np.arange(1,2**n);x=((sample[:,None]>>np.arange(n))&1).astype(float)
    theta=np.r_[u.ravel(),logp.ravel()]
    score=lambda t:mixed_score_jac(t,x,n,h,orientation)
    raw=score(theta)[0]-1;y=np.where(raw<0,-1.,1.)
    theta[:k]*=2.1/np.min(abs(raw[raw<0]))
    norm_scale=max(1.,np.dot(theta[:k],theta[:k]));cache={}
    def evaluate(t):
        if 'theta' not in cache or not np.array_equal(t,cache['theta']):
            v,j=score(t);cache.update(theta=t.copy(),value=v,jac=j)
        return cache
    def objective(t):return np.dot(t[:k],t[:k])/norm_scale
    def gradient(t):return np.r_[2*t[:k]/norm_scale,np.zeros(k)]
    result=minimize(objective,theta,jac=gradient,method='SLSQP',
        bounds=[(None,None)]*k+[(-12.,12.)]*k,
        constraints=[dict(type='ineq',fun=lambda t:y*evaluate(t)['value']-1,
          jac=lambda t:y[:,None]*evaluate(t)['jac'])],
        options=dict(maxiter=3000,ftol=1e-11,disp=False))
    refinement_log=[]
    for stage in range(a.refinements):
        theta=result.x.copy();norm_scale=max(1.,np.dot(theta[:k],theta[:k]))
        result=minimize(objective,theta,jac=gradient,method='SLSQP',
            bounds=[(None,None)]*k+[(-12.,12.)]*k,
            constraints=[dict(type='ineq',fun=lambda t:y*evaluate(t)['value']-1,
              jac=lambda t:y[:,None]*evaluate(t)['jac'])],
            options=dict(maxiter=5000,ftol=1e-13,disp=False))
        refinement_log.append(dict(stage=stage,norm_scale=norm_scale,
            status=int(result.status),iterations=int(result.nit),
            norm=float(result.x[:k]@result.x[:k])))
    theta=result.x;value,jac=score(theta);slack=y*value-1
    active=np.flatnonzero(slack<1e-6);signed=y[active,None]*jac[active]
    grad=gradient(theta)*norm_scale
    dual,residual=nnls(signed.T,grad,maxiter=100000)
    tangent=null_space(signed,rcond=1e-9)
    def lagrangian_gradient(t):
        return gradient(t)*norm_scale-score(t)[1][active].T@(y[active]*dual)
    curvature=[]
    for step in [1e-4,1e-5,1e-6]:
        columns=[]
        for j in range(2*k):
            direction=np.zeros(2*k);direction[j]=step
            columns.append((lagrangian_gradient(theta+direction)-lagrangian_gradient(theta-direction))/(2*step))
        hh=np.column_stack(columns);sym=(hh+hh.T)/2
        eig=np.linalg.eigvalsh(tangent.T@sym@tangent)
        curvature.append(dict(step=step,asymmetry=float(np.max(abs(hh-hh.T))),
          tangent_eigenvalues=eig.tolist()))
    out=dict(status='NUMERICAL_KKT_DIAGNOSTIC_ONLY',trial=trial,n=n,heads=h,
        solver_status=int(result.status),iterations=int(result.nit),
        min_slack=float(slack.min()),active_count=len(active),parameter_count=2*k,
        norm=float(theta[:k]@theta[:k]),log_bound_distance=float(12-max(abs(theta[k:]))),
        multiplier_residual=float(residual),relative_multiplier_residual=float(residual/max(1,np.linalg.norm(grad))),
        active_singular_values=np.linalg.svd(signed,compute_uv=False).tolist(),
        tangent_dimension=int(tangent.shape[1]),curvature=curvature,
        theta=theta.tolist(),orientation=orientation.tolist(),labels=y.tolist(),
        refinements=refinement_log,
        active_vertices=sample[active].tolist(),multipliers=dual.tolist(),
        main_target_proved=False,elapsed_seconds=time.monotonic()-start)
    a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ['theta','labels','multipliers','curvature','active_singular_values']}))


if __name__=='__main__':main()
