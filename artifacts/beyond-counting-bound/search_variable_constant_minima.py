"""Numerical search for full-cube numerator-norm minima with free constant.

All records are exploratory. A candidate requires an independent exact or
interval certificate before it can support any theorem. Denominator slopes
have one coherent sign per head, and every Boolean vertex is constrained.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from search_full_cube_unit_minima import mixed_score_jac,check_mixed_gradient


def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
 p.add_argument('--seconds',type=float,default=7200);p.add_argument('--seed',type=int,default=710295)
 args=p.parse_args();args.output.mkdir(parents=True,exist_ok=True)
 rng=np.random.default_rng(args.seed);start=time.monotonic();trial=0
 print(json.dumps({'mixed_gradient_check':check_mixed_gradient()}),flush=True)
 class Expired(Exception):pass
 with (args.output/'results.jsonl').open('a',buffering=1) as log:
  while time.monotonic()-start<args.seconds:
   n,h=[(6,3),(7,3),(7,4),(8,4),(8,5)][trial%5];k=n*h;pcount=1+2*k
   orientation=rng.choice([-1.,1.],size=h)
   sample=np.arange(2**n);x=((sample[:,None]>>np.arange(n))&1).astype(float)
   u=rng.normal(size=(n,h));logp=rng.uniform(-2,2,size=(n,h))
   if trial%3==0:
    u-=u.mean(axis=1,keepdims=True)
    logp=rng.uniform(-1,1,size=(n,1))+rng.normal(scale=0.5,size=(n,h))
   def score_jac(t):
    v,j=mixed_score_jac(t[1:],x,n,h,orientation)
    return v-1+t[0],np.c_[np.ones(len(x)),j]
   theta=np.r_[0.,u.ravel(),logp.ravel()]
   raw,_=score_jac(theta)
   c=-float(np.quantile(raw,rng.uniform(.2,.8)))
   theta[0]=c;value=raw+c
   if min(abs(value))<1e-5:
    trial+=1;continue
   theta[:1+k]*=1.1/min(abs(value));y=np.sign(value)
   norm_scale=max(1.,np.dot(theta[:1+k],theta[:1+k]));cache={}
   def evaluate(t):
    if time.monotonic()-start>=args.seconds:raise Expired
    if 'theta' not in cache or not np.array_equal(t,cache['theta']):
     v,j=score_jac(t);cache.update(theta=t.copy(),value=v,jac=j)
    return cache
   def objective(t):return np.dot(t[:1+k],t[:1+k])/norm_scale
   def gradient(t):return np.r_[2*t[:1+k]/norm_scale,np.zeros(k)]
   try:
    result=minimize(objective,theta,jac=gradient,method='SLSQP',
      bounds=[(None,None)]*(1+k)+[(-12.,12.)]*k,
      constraints=[dict(type='ineq',fun=lambda t:y*evaluate(t)['value']-1,
       jac=lambda t:y[:,None]*evaluate(t)['jac'])],
      options=dict(maxiter=3000,ftol=1e-11,disp=False))
    refinement_log=[]
    for stage in range(3):
     theta=result.x.copy();norm_scale=max(1.,np.dot(theta[:1+k],theta[:1+k]))
     result=minimize(objective,theta,jac=gradient,method='SLSQP',
       bounds=[(None,None)]*(1+k)+[(-12.,12.)]*k,
       constraints=[dict(type='ineq',fun=lambda t:y*evaluate(t)['value']-1,
         jac=lambda t:y[:,None]*evaluate(t)['jac'])],
       options=dict(maxiter=5000,ftol=1e-13,disp=False))
     refinement_log.append(dict(stage=stage,norm_scale=float(norm_scale),
       solver_status=int(result.status),iterations=int(result.nit)))
    value,jac=score_jac(result.x);slack=y*value-1;active=np.flatnonzero(slack<1e-6)
    boundary=float(12-np.max(abs(result.x[1+k:])))
    record=dict(trial=trial,n=n,heads=h,status='UNKNOWN',solver_status=int(result.status),
      nit=int(result.nit),min_slack=float(slack.min()),active_count=len(active),
      parameter_count=pcount,log_bound_distance=boundary,
      numerator_norm=float(np.dot(result.x[:1+k],result.x[:1+k])),
      constant=float(result.x[0]),elapsed_seconds=time.monotonic()-start)
    record['refinements']=refinement_log
    if len(active)>=pcount and slack.min()>-1e-7 and boundary>1e-3:
     from scipy.linalg import qr
     signed=y[:,None]*jac
     _,_,piv=qr(signed[active].T,pivoting=True,mode='economic')
     chosen=active[piv[:pcount]];matrix=signed[chosen];sv=np.linalg.svd(matrix,compute_uv=False)
     record['min_singular']=float(sv[-1])
     if sv[-1]>1e-9:
      dual=np.linalg.solve(matrix.T,gradient(result.x)*norm_scale)
      record['min_multiplier']=float(dual.min());record['status']='FLOATING_INTERIOR_ACTIVE_CANDIDATE'
      if dual.min()>1e-7:record['status']='FLOATING_POSITIVE_DUAL_CANDIDATE'
      data=dict(record,theta=result.x.tolist(),orientation=orientation.tolist(),labels=y.tolist(),
       active_indices=chosen.tolist(),active_vertices=sample[chosen].tolist(),multipliers=dual.tolist(),
       slack=slack.tolist(),main_target_proved=False)
      name=f'candidate-{trial}.json';(args.output/name).write_text(json.dumps(data,indent=2)+'\n');record['candidate']=name
    log.write(json.dumps(record)+'\n')
    if trial%25==0 or 'candidate' in record:print(json.dumps(record),flush=True)
   except Expired:break
   except (ValueError,np.linalg.LinAlgError,FloatingPointError) as exc:
    log.write(json.dumps(dict(trial=trial,status='NUMERICAL_FAILURE_UNKNOWN',error=type(exc).__name__))+'\n')
   trial+=1
 print(json.dumps(dict(status='SEARCH_FINISHED_UNKNOWN',trials=trial,elapsed_seconds=time.monotonic()-start,main_target_proved=False)),flush=True)


if __name__=='__main__':main()
