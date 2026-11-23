"""Adversarial full-cube unit-minimum search at parity's exact head count.

Starting residues are solved over Q, with poles outside the complete Hamming
weight interval. All nonorigin cube values start at twice the parity sign.
Small nonsymmetric perturbations are accepted only if every cube inequality
remains feasible. Numerical candidates require a subsequent exact certificate.
Run with heavy and single-thread BLAS.
"""
import argparse
import json
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
import sympy as sp
from scipy.optimize import linprog,minimize

from search_full_cube_unit_minima import mixed_score_jac,check_mixed_gradient


def exact_seed(n, offset=0):
    h=n
    distances=[Fraction(1,100),Fraction(1,10),Fraction(1),Fraction(10),Fraction(100),Fraction(1000)]
    poles=[]
    for j in range(n):
        distance=distances[j//2]*Fraction(2+offset,2)
        poles.append(-distance if j%2==0 else n+distance)
    slopes=[-1/p for p in poles]
    matrix=sp.Matrix([[sp.Rational(Fraction(k)/(1+b*k)) for b in slopes] for k in range(1,n+1)])
    target=sp.Matrix([2*((-1)**k)-1 for k in range(1,n+1)])
    residue=matrix.inv()*target
    residues=[Fraction(int(z.p),int(z.q)) for z in residue]
    for k in range(1,n+1):
        assert 1+sum((a*k/(1+b*k) for a,b in zip(residues,slopes)),Fraction(0))==2*((-1)**k)
    orientation=np.array([1 if b>0 else -1 for b in slopes])
    p=np.array([float(b if b>0 else -b/(1+n*b)) for b in slopes])
    unscaled=np.array([float(a) for a in residues])
    scale=max(1.,float(np.max(abs(unscaled))))
    theta=np.r_[np.tile(unscaled/scale,n),np.tile(np.log(p),n)]
    return theta,orientation,2/scale,dict(poles=[str(p) for p in poles],residues=[str(a) for a in residues],
                                        common_float_scale=scale)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=7200)
    ap.add_argument('--trial-seconds',type=float,default=300)
    ap.add_argument('--seed',type=int,default=73620911);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    print(json.dumps(dict(status='DERIVATIVE_CHECK_PASS',error=check_mixed_gradient())),flush=True)
    rng=np.random.default_rng(args.seed);start=time.monotonic();trial=0
    class Expired(Exception):pass
    with (args.output/'results.jsonl').open('a',buffering=1) as log:
        while time.monotonic()-start<args.seconds:
            n=[7,8,9,10][trial%4];h=n;d=n*h;pcount=2*d
            vertices=np.arange(1,1<<n);x=((vertices[:,None]>>np.arange(n))&1).astype(float)
            y=np.where(x.sum(axis=1).astype(int)%2==0,1.,-1.)
            theta,orientation,gamma,seed_data=exact_seed(n,(trial//4)%5)
            raw=mixed_score_jac(theta,x,n,h,orientation)[0]-1
            error=float(np.max(abs(raw-((2*y-1)*gamma/2))))
            assert error<1e-7*gamma,(n,error,gamma)
            _,initial_jac=mixed_score_jac(theta,x,n,h,orientation)
            column_norm=np.maximum(np.linalg.norm(initial_jac,axis=0),1e-14)
            _,singular,vh=np.linalg.svd(initial_jac/column_norm[None,:],full_matrices=False)
            null=vh[singular<1e-10]
            direction=(rng.normal(size=len(null))@null)/column_norm if len(null) else rng.normal(size=pcount)
            direction/=max(1e-16,float(np.max(abs(direction))))
            accepted=0.
            for perturbation in [1e-1,1e-2,1e-3,1e-4,1e-5,1e-6,1e-7,1e-8,1e-9,1e-10,1e-11,1e-12]:
                t=theta+perturbation*direction
                value=mixed_score_jac(t,x,n,h,orientation)[0]-1
                if np.min(y*value-gamma*(y<0))>1e-3*gamma:
                    theta=t;accepted=perturbation;break
            begin=time.monotonic();history=[];cache={}
            def evaluate(t):
                if time.monotonic()-start>args.seconds or time.monotonic()-begin>args.trial_seconds:raise Expired
                if 'theta' not in cache or not np.array_equal(cache['theta'],t):
                    value,jac=mixed_score_jac(t,x,n,h,orientation)
                    cache.update(theta=t.copy(),value=value-1,jac=jac)
                return cache
            try:
                for stage in range(3):
                    norm_scale=max(1e-16,float(theta[:d]@theta[:d]))
                    result=minimize(lambda t:.5*float(t[:d]@t[:d])/norm_scale,theta,
                        jac=lambda t:np.r_[t[:d]/norm_scale,np.zeros(d)],method='SLSQP',
                        bounds=[(None,None)]*d+[(-18.,18.)]*d,
                        constraints=[dict(type='ineq',fun=lambda t:y*evaluate(t)['value']-gamma*(y<0),
                                          jac=lambda t:y[:,None]*evaluate(t)['jac'])],
                        options=dict(maxiter=2000,ftol=1e-13,disp=False))
                    theta=result.x
                    value,jac=mixed_score_jac(theta,x,n,h,orientation);slack=y*(value-1)-gamma*(y<0)
                    history.append(dict(stage=stage,solver_status=int(result.status),iterations=int(result.nit),
                        relative_slack=float(slack.min()/gamma),norm=float(theta[:d]@theta[:d]),
                        boundary_distance=float(18-np.max(abs(theta[d:])))))
                active=np.flatnonzero(slack<=max(1e-12,1e-5*gamma))
                active_scale=np.maximum(np.linalg.norm(jac[active],axis=0),1e-14)
                sv=float(np.linalg.svd(jac[active]/active_scale[None,:],compute_uv=False)[-1]) if len(active)>=pcount else 0.
                record=dict(trial=trial,n=n,heads=h,gamma=gamma,seed_rounding_error=error,perturbation=accepted,
                            active_count=len(active),parameter_count=pcount,column_normalized_min_singular=sv,history=history,
                            status='UNKNOWN',elapsed_seconds=time.monotonic()-start)
                if slack.min()>-1e-7*gamma and history[-1]['boundary_distance']>1e-3 and sv>1e-12:
                    signed=y[active,None]*jac[active];gradient=np.r_[theta[:d],np.zeros(d)]
                    m=len(active);scale=np.maximum(np.linalg.norm(signed,axis=0),1e-14)
                    mat=signed.T/scale[:,None];rhs=gradient/scale
                    lp=linprog(np.r_[np.zeros(m),-1.],A_eq=np.c_[mat,np.zeros(pcount)],b_eq=rhs,
                        A_ub=np.c_[-np.eye(m),np.ones(m)],b_ub=np.zeros(m),
                        bounds=[(0,None)]*m+[(None,None)],method='highs')
                    record.update(status='FLOATING_FULL_RANK_CANDIDATE',dual_status=int(lp.status),
                                  min_multiplier=float(lp.x[-1]) if lp.success else None)
                    if lp.success and lp.x[-1]>1e-9:record['status']='FLOATING_POSITIVE_DUAL_CANDIDATE'
                    name=f'candidate-{trial}.json'
                    data=dict(record,theta=theta.tolist(),orientation=orientation.tolist(),labels=y.tolist(),
                              active_vertices=vertices[active].tolist(),seed=seed_data,
                              multipliers=lp.x[:-1].tolist() if lp.success else None,main_target_proved=False)
                    (args.output/name).write_text(json.dumps(data,indent=2)+'\n');record['candidate']=name
            except Expired:
                record=dict(trial=trial,n=n,heads=h,status='TIME_LIMIT_UNKNOWN',history=history,
                            elapsed_seconds=time.monotonic()-start)
            except (ValueError,np.linalg.LinAlgError,FloatingPointError) as exc:
                record=dict(trial=trial,n=n,status='NUMERICAL_FAILURE_UNKNOWN',error=str(exc))
            log.write(json.dumps(record)+'\n')
            print(json.dumps({a:b for a,b in record.items() if a!='history'}),flush=True)
            trial+=1
    print(json.dumps(dict(status='FINISHED_UNKNOWN',trials=trial,elapsed_seconds=time.monotonic()-start)),flush=True)


if __name__=='__main__':main()
