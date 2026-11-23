"""Exploratory unit-margin minimization of actual head-table energy.

The objective is c^2 + mean_x sum_h r_h(x)^2, not a norm of coefficients.
All Boolean constraints and coherent denominator orientations are retained.
Every floating result requires an independent exact or interval certificate.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog,minimize
from search_full_cube_unit_minima import mixed_score_jac


def evaluate(theta,x,n,h,orientation):
    k=n*h;t=theta[1:]
    u=t[:k].reshape(n,h);p=np.exp(t[k:].reshape(n,h));c=1+p.sum(axis=0)
    den=np.where(orientation[None,:]>0,1+x@p,(1+(1-x)@p)/c[None,:])
    r=(x@u)/den
    value,jac=mixed_score_jac(t,x,n,h,orientation)
    head_index=np.tile(np.arange(h),2*n)
    energy=theta[0]**2+np.mean(np.sum(r*r,axis=1))
    gradient=np.r_[2*theta[0],2*np.mean(jac*r[:,head_index],axis=0)]
    return value-1+theta[0],np.c_[np.ones(len(x)),jac],energy,gradient


def check_gradient():
    rng=np.random.default_rng(351);n,h=4,3
    x=rng.integers(0,2,(20,n));t=rng.normal(size=1+2*n*h);ori=np.array([1,-1,1])
    grad=evaluate(t,x,n,h,ori)[3];errors=[]
    for i in range(len(t)):
        delta=np.zeros_like(t);delta[i]=1e-6
        fd=(evaluate(t+delta,x,n,h,ori)[2]-evaluate(t-delta,x,n,h,ori)[2])/2e-6
        errors.append(abs(fd-grad[i]))
    assert max(errors)<1e-7
    return max(errors)


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=5400);p.add_argument('--seed',type=int,default=209341)
    p.add_argument('--log-bound',type=float,default=12.)
    p.add_argument('--replay',type=int)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    rng=np.random.default_rng(a.seed);start=time.monotonic();trial=0;linear_skips=0
    print(json.dumps({'energy_gradient_error':check_gradient()}),flush=True)
    class Expired(Exception):pass
    with (a.output/'results.jsonl').open('a',buffering=1) as log:
        while time.monotonic()-start<a.seconds:
            if a.replay is not None and trial>a.replay:break
            n,h=[(6,3),(7,3),(7,4),(8,4)][trial%4];k=n*h;pcount=1+2*k
            x=((np.arange(2**n)[:,None]>>np.arange(n))&1).astype(float)
            ori=rng.choice([-1.,1.],size=h);u=rng.normal(size=(n,h));logp=rng.uniform(-3,3,size=(n,h))
            if trial%3==0:
                u-=u.mean(axis=1,keepdims=True)
                logp=rng.uniform(-1,1,size=(n,1))+rng.normal(scale=.7,size=(n,h))
            theta=np.r_[0.,u.ravel(),logp.ravel()]
            raw=evaluate(theta,x,n,h,ori)[0]
            theta[0]=-np.quantile(raw,rng.uniform(.15,.85));values=raw+theta[0]
            if min(abs(values))<1e-5:trial+=1;continue
            y=np.sign(values)
            if a.replay is not None and trial!=a.replay:trial+=1;continue
            lp=linprog(np.zeros(n+1),A_ub=-y[:,None]*np.c_[np.ones(len(x)),x],
                b_ub=-np.ones(len(x)),bounds=[(None,None)]*(n+1),method='highs')
            if lp.status!=2:
                linear_skips+=1;trial+=1;continue
            theta[:1+k]*=1.1/min(abs(values));scale=evaluate(theta,x,n,h,ori)[2];cache={}
            def ev(t):
                if time.monotonic()-start>=a.seconds:raise Expired
                if 'theta' not in cache or not np.array_equal(cache['theta'],t):
                    v,j,e,g=evaluate(t,x,n,h,ori);cache.update(theta=t.copy(),value=v,jac=j,energy=e,gradient=g)
                return cache
            try:
                stages=[]
                for stage in range(3):
                    scale=max(1.,evaluate(theta,x,n,h,ori)[2])
                    result=minimize(lambda t:ev(t)['energy']/scale,theta,
                        jac=lambda t:ev(t)['gradient']/scale,method='SLSQP',
                        bounds=[(None,None)]*(1+k)+[(-a.log_bound,a.log_bound)]*k,
                        constraints=[dict(type='ineq',fun=lambda t:y*ev(t)['value']-1,
                            jac=lambda t:y[:,None]*ev(t)['jac'])],
                        options=dict(maxiter=4000,ftol=1e-12,disp=False))
                    theta=result.x;stages.append(dict(stage=stage,status=int(result.status),nit=int(result.nit)))
                v,j,e,g=evaluate(theta,x,n,h,ori);slack=y*v-1;active=np.flatnonzero(slack<1e-6)
                boundary=float(a.log_bound-max(abs(theta[1+k:])))
                rec=dict(status='UNKNOWN',trial=trial,n=n,heads=h,parameter_count=pcount,
                    active_count=len(active),min_slack=float(slack.min()),log_bound_distance=boundary,
                    energy=float(e),stages=stages,linear_label_skips=linear_skips,
                    elapsed_seconds=time.monotonic()-start,main_target_proved=False)
                if len(active)>=pcount and slack.min()>-1e-7 and boundary>1e-3:
                    from scipy.linalg import qr
                    signed=y[:,None]*j
                    _,_,piv=qr(signed[active].T,pivoting=True,mode='economic')
                    chosen=active[piv[:pcount]];matrix=signed[chosen];sv=np.linalg.svd(matrix,compute_uv=False)
                    rec['min_singular']=float(sv[-1])
                    if sv[-1]>1e-9:
                        dual=np.linalg.solve(matrix.T,g);rec['minimum_multiplier']=float(dual.min())
                        rec['status']='FLOATING_INTERIOR_ACTIVE_CANDIDATE'
                        if dual.min()>1e-7:rec['status']='FLOATING_POSITIVE_DUAL_CANDIDATE'
                        name=f'candidate-{trial}.json';rec['candidate']=name
                        data=dict(rec,theta=theta.tolist(),orientation=ori.tolist(),labels=y.tolist(),
                            active_vertices=chosen.tolist(),multipliers=dual.tolist(),slack=slack.tolist())
                        (a.output/name).write_text(json.dumps(data,indent=2)+'\n')
                log.write(json.dumps(rec)+'\n');print(json.dumps(rec),flush=True)
                if a.replay is not None:
                    data=dict(rec,theta=theta.tolist(),orientation=ori.tolist(),labels=y.tolist(),
                        active_vertices=active.tolist(),gradient=g.tolist(),slack=slack.tolist())
                    (a.output/'replay.json').write_text(json.dumps(data,indent=2)+'\n')
            except Expired:break
            except (ValueError,np.linalg.LinAlgError,FloatingPointError) as exc:
                log.write(json.dumps(dict(status='NUMERICAL_FAILURE_UNKNOWN',trial=trial,error=type(exc).__name__))+'\n')
            trial+=1
    print(json.dumps(dict(status='SEARCH_FINISHED_UNKNOWN',trials=trial,
        elapsed_seconds=time.monotonic()-start,main_target_proved=False)),flush=True)


if __name__=='__main__':main()
