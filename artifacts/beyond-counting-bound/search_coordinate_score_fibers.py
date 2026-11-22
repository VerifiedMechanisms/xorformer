"""Numerical search for positive fibers of actual Boolean evaluation maps.

This is not a head lower bound. A small floating residual is only a candidate;
an independent interval proof is required before claiming an exact fiber.
Run sustained searches through `heavy`.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np
from scipy.linalg import qr
from scipy.optimize import least_squares


def score_jac(theta, x, n, h):
    u = theta[:n*h].reshape(n, h)
    b = np.exp(theta[n*h:].reshape(n, h))
    den = 1 + x @ b
    num = x @ u
    value = 1 + (num/den).sum(axis=1)
    ju = (x[:, :, None]/den[:, None, :]).reshape(len(x), n*h)
    jb = (-x[:, :, None] * (num/den**2)[:, None, :]
          * b[None, :, :]).reshape(len(x), n*h)
    return value, np.concatenate([ju, jb], axis=1)


def check_gradient():
    rng = np.random.default_rng(4141)
    x = rng.integers(0, 2, size=(10, 4)).astype(float)
    theta = rng.normal(size=24)
    value, jac = score_jac(theta, x, 4, 3)
    errors = []
    for i in range(len(theta)):
        d = np.zeros_like(theta); d[i] = 1e-6
        numeric = (score_jac(theta+d,x,4,3)[0]-
                   score_jac(theta-d,x,4,3)[0])/2e-6
        errors.append(float(np.max(np.abs(numeric-jac[:,i]))))
    assert max(errors) < 1e-7
    return max(errors)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--seconds', type=float, default=18000)
    p.add_argument('--n', type=int, default=6)
    p.add_argument('--heads', type=int, default=3)
    p.add_argument('--seed', type=int, default=730741)
    p.add_argument('--max-evals', type=int, default=1500)
    p.add_argument('--check-only', action='store_true')
    args = p.parse_args()
    print(json.dumps({'event':'gradient_check','error':check_gradient()}),flush=True)
    if args.check_only:
        return
    n,h=args.n,args.heads
    assert 2*n*h < 2**n-1 and h >= 3
    out=args.output;out.mkdir(parents=True,exist_ok=True)
    rng=np.random.default_rng(args.seed)
    x=((np.arange(2**n)[:,None]>>np.arange(n))&1).astype(float)
    # All starting coefficients are exactly specified rationals.
    b_int=rng.integers(1,33,size=(n,h))
    u_int=-b_int + rng.integers(-20,21,size=(n,h))
    b0=b_int/8;u0=u_int/(8*h)
    original=np.r_[u0.ravel(),np.log(b0).ravel()]
    values,jac=score_jac(original,x,n,h)
    _,_,piv=qr(jac[1:].T,pivoting=True,mode='economic')
    sample=np.sort(piv[:2*n*h]+1)
    sv=np.linalg.svd(jac[sample],compute_uv=False)
    config=dict(n=n,heads=h,seed=args.seed,sample=sample.tolist(),
                numerator_integer=u_int.tolist(),numerator_scale=8*h,
                denominator_integer=b_int.tolist(),denominator_scale=8,
                base_min_singular_value=float(sv[-1]),
                scope='actual full Boolean-cube evaluation map',
                status='NUMERICAL_SEARCH_ONLY',main_target_proved=False)
    (out/'config.json').write_text(json.dumps(config,indent=2)+'\n')
    print(json.dumps(config),flush=True)
    target=values[sample];xs=x[sample]
    started=time.monotonic();deadline=started+args.seconds
    trial=0;distinct=[];last_progress=started
    class BudgetExpired(Exception): pass
    with (out/'results.jsonl').open('a',buffering=1) as log:
        while time.monotonic()<deadline:
            if trial%4==0:
                # Break head matching independently in every coordinate.
                ub=np.stack([rng.permutation(h) for _ in range(n)])
                v=np.take_along_axis(u0,ub,axis=1)
                w=np.take_along_axis(b0,ub,axis=1)
                initial=np.r_[v.ravel(),np.log(w).ravel()]
                initial+=rng.normal(0,.15,size=len(initial))
            elif trial%4==1:
                initial=original+rng.normal(0,.8,size=len(original))
            else:
                initial=np.r_[rng.normal(-1,2,size=n*h),
                              rng.uniform(-4,4,size=n*h)]
            cached={}
            def evaluate(t):
                if time.monotonic()>deadline: raise BudgetExpired
                if 'theta' not in cached or not np.array_equal(cached['theta'],t):
                    val,j=score_jac(t,xs,n,h)
                    cached.update(theta=t.copy(),residual=val-target,jac=j)
                return cached
            try:
                result=least_squares(lambda t:evaluate(t)['residual'],initial,
                    jac=lambda t:evaluate(t)['jac'],method='trf',
                    bounds=(np.r_[np.full(n*h,-1e4),np.full(n*h,-10)],
                            np.r_[np.full(n*h,1e4),np.full(n*h,10)]),
                    x_scale='jac',ftol=1e-13,xtol=1e-13,gtol=1e-13,
                    max_nfev=args.max_evals)
            except BudgetExpired:
                break
            full,fulljac=score_jac(result.x,x,n,h)
            residual=float(np.max(np.abs(full[sample]-target)))
            difference=float(np.max(np.abs(full-values)))
            distance=min([float(np.max(np.abs(full-old))) for old in distinct]
                         or [float('inf')])
            record=dict(trial=trial,seconds=time.monotonic()-started,
                nfev=int(result.nfev),residual=residual,
                unsampled_difference=difference,status='UNKNOWN')
            if residual<1e-9 and difference>1e-5 and distance>1e-5:
                singular=np.linalg.svd(fulljac[sample],compute_uv=False)
                record.update(status='FLOATING_CANDIDATE_NOT_CERTIFICATE',
                    min_singular_value=float(singular[-1]),
                    coefficient_min=float(np.min(np.exp(result.x[n*h:]))))
                candidate=dict(config,**{'trial':trial,'theta':result.x.tolist(),
                    'full_values':full.tolist(),'diagnostic':record})
                name=f'candidate-{trial}.json'
                (out/name).write_text(json.dumps(candidate,indent=2)+'\n')
                record['candidate']=name;distinct.append(full)
            log.write(json.dumps(record)+'\n')
            now=time.monotonic()
            if 'candidate' in record or now-last_progress>60:
                print(json.dumps(record),flush=True);last_progress=now
            trial+=1
    print(json.dumps({'event':'finished','trials':trial,'candidates':len(distinct),
        'elapsed_seconds':time.monotonic()-started,'status':'UNKNOWN',
        'main_target_proved':False}),flush=True)


if __name__=='__main__':
    main()
