"""Search full-cube unit-margin local minima with fixed score constant one.

Candidate labels come from sign(S-1); scaling numerators then supplies a known
feasible initial point. SLSQP optimizes the actual numerator norm. Every result
is UNKNOWN unless later certified with exact interval arithmetic.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from search_coordinate_score_fibers import check_gradient


def mixed_score_jac(theta,x,n,h,orientation):
 u=theta[:n*h].reshape(n,h);p=np.exp(theta[n*h:].reshape(n,h))
 c=1+p.sum(axis=0);b=np.where(orientation[None,:]>0,p,-p/c[None,:])
 den=1+x@b;num=x@u;value=1+(num/den).sum(axis=1)
 ju=(x[:,:,None]/den[:,None,:]).reshape(len(x),n*h)
 dp=x[:,:,None]*p[None,:,:]
 negative_dp=-dp/c[None,None,:]+(x@p)[:,None,:]*p[None,:,:]/c[None,None,:]**2
 dd=np.where(orientation[None,None,:]>0,dp,negative_dp)
 jb=(-dd*(num/den**2)[:,None,:]).reshape(len(x),n*h)
 return value,np.c_[ju,jb]


def check_mixed_gradient():
 rng=np.random.default_rng(83451);n,h=4,3
 x=rng.integers(0,2,(12,n));theta=rng.normal(size=2*n*h);orientation=np.array([1,-1,-1])
 _,j=mixed_score_jac(theta,x,n,h,orientation);errors=[]
 for k in range(len(theta)):
  d=np.zeros_like(theta);d[k]=1e-6
  difference=(mixed_score_jac(theta+d,x,n,h,orientation)[0]-mixed_score_jac(theta-d,x,n,h,orientation)[0])/2e-6
  errors.append(float(np.max(abs(difference-j[:,k]))))
 assert max(errors)<1e-7
 return max(errors)


def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
 p.add_argument('--seconds',type=float,default=7200);p.add_argument('--seed',type=int,default=119084)
 p.add_argument('--mode',choices=['independent','cancellation','mixed'],default='independent')
 args=p.parse_args();args.output.mkdir(parents=True,exist_ok=True)
 rng=np.random.default_rng(args.seed);start=time.monotonic();trial=0
 print(json.dumps({'gradient_check':check_gradient(),'mixed_gradient_check':check_mixed_gradient()}),flush=True)
 class Expired(Exception):pass
 with (args.output/'results.jsonl').open('a',buffering=1) as log:
  while time.monotonic()-start<args.seconds:
   n,h=[(6,3),(7,3),(7,4),(8,4)][trial%4];pcount=2*n*h
   orientation=np.ones(h) if args.mode!='mixed' else rng.choice([-1.,1.],size=h)
   score_jac=lambda t,xx,nn,hh:mixed_score_jac(t,xx,nn,hh,orientation)
   sample=np.arange(1,2**n);x=((sample[:,None]>>np.arange(n))&1).astype(float)
   u=rng.normal(size=(n,h));logp=rng.uniform(-2,2,size=(n,h))
   if args.mode=='cancellation' or (args.mode=='mixed' and trial%3==0):
    u-=u.mean(axis=1,keepdims=True)
    logp=rng.uniform(-1,1,size=(n,1))+rng.normal(scale=0.5,size=(n,h))
   theta=np.r_[u.ravel(),logp.ravel()]
   value,_=score_jac(theta,x,n,h);raw=value-1
   # Both labels and a safe finite initial scale.
   if raw.min()>=-1e-5 or raw.max()<=1e-5:
    trial+=1;continue
   negative=raw<0;scale=2.1/np.min(abs(raw[negative]))
   if scale>1e4:
    trial+=1;continue
   theta[:n*h]*=scale;y=np.where(negative,-1.,1.)
   norm_scale=max(1.,np.dot(theta[:n*h],theta[:n*h]))
   cache={}
   def evaluate(t):
    if time.monotonic()-start>=args.seconds:raise Expired
    if 'theta' not in cache or not np.array_equal(t,cache['theta']):
     v,j=score_jac(t,x,n,h);cache.update(theta=t.copy(),value=v,jac=j)
    return cache
   def objective(t):return np.dot(t[:n*h],t[:n*h])/norm_scale
   def gradient(t):return np.r_[2*t[:n*h]/norm_scale,np.zeros(n*h)]
   try:
    result=minimize(objective,theta,jac=gradient,method='SLSQP',
      bounds=[(None,None)]*(n*h)+[(-12.,12.)]*(n*h),
      constraints=[dict(type='ineq',fun=lambda t:y*evaluate(t)['value']-1,
       jac=lambda t:y[:,None]*evaluate(t)['jac'])],
      options=dict(maxiter=3000,ftol=1e-11,disp=False))
    value,jac=score_jac(result.x,x,n,h);slack=y*value-1
    active=np.flatnonzero(slack<1e-6)
    near_boundary=float(12-np.max(abs(result.x[n*h:])))
    record=dict(trial=trial,n=n,heads=h,mode=args.mode,status='UNKNOWN',solver_status=int(result.status),
      nit=int(result.nit),min_slack=float(slack.min()),active_count=len(active),
      parameter_count=pcount,log_bound_distance=near_boundary,
      numerator_norm=float(np.dot(result.x[:n*h],result.x[:n*h])),
      elapsed_seconds=time.monotonic()-start)
    if len(active)>=pcount and slack.min()>-1e-7 and near_boundary>1e-3:
     from scipy.linalg import qr
     signed=y[:,None]*jac
     _,_,piv=qr(signed[active].T,pivoting=True,mode='economic')
     chosen=active[piv[:pcount]];matrix=signed[chosen]
     sv=np.linalg.svd(matrix,compute_uv=False)
     record['min_singular']=float(sv[-1])
     if sv[-1]>1e-9:
      dual=np.linalg.solve(matrix.T,gradient(result.x)*norm_scale)
      record['min_multiplier']=float(dual.min())
      record['status']='FLOATING_INTERIOR_ACTIVE_CANDIDATE'
      if dual.min()>1e-7:record['status']='FLOATING_POSITIVE_DUAL_CANDIDATE'
      data=dict(record,theta=result.x.tolist(),orientation=orientation.tolist(),labels=y.tolist(),sample_indices=sample.tolist(),
       active_indices=chosen.tolist(),active_vertices=sample[chosen].tolist(),
       multipliers=dual.tolist(),slack=slack.tolist(),main_target_proved=False)
      name=f'candidate-{trial}.json';(args.output/name).write_text(json.dumps(data,indent=2)+'\n')
      record['candidate']=name
    log.write(json.dumps(record)+'\n')
    if trial%25==0 or 'candidate' in record:print(json.dumps(record),flush=True)
   except Expired:break
   except (ValueError,np.linalg.LinAlgError,FloatingPointError) as exc:
    log.write(json.dumps(dict(trial=trial,status='NUMERICAL_FAILURE_UNKNOWN',error=type(exc).__name__))+'\n')
   trial+=1
 print(json.dumps(dict(status='SEARCH_FINISHED_UNKNOWN',trials=trial,elapsed_seconds=time.monotonic()-start,main_target_proved=False)),flush=True)


if __name__=='__main__':main()
