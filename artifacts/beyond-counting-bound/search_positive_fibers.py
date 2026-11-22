#!/usr/bin/env python3
"""Search only: positive fibers of the cube evaluation map.

Numerical roots are candidates, not certified counterexamples. No failure is
interpreted as injectivity or as a head-complexity lower bound.
"""
import argparse
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import least_squares


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--starts', type=int, default=1000)
    ap.add_argument('--seed', type=int, default=480331)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    n, heads = 5, 2
    cube = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    indices = np.sort(rng.choice(np.arange(1, 1 << n), 2*n*heads, replace=False))
    x = cube[indices]
    b_num = rng.integers(2, 21, (heads, n))
    u_num = rng.integers(-20, 21, (heads, n))
    b0, u0 = b_num/10, u_num/10
    def evaluate(p, inputs=x):
        u, b = p[:heads*n].reshape(heads,n), p[heads*n:].reshape(heads,n)
        return ((inputs@u.T)/(1+inputs@b.T)).sum(axis=1)
    source = np.r_[u0.ravel(), b0.ravel()]
    y = evaluate(source)
    def fun(p): return evaluate(p)-y
    def jac(p):
        u, b = p[:heads*n].reshape(heads,n), p[heads*n:].reshape(heads,n)
        d = 1+x@b.T
        a = x@u.T
        return np.c_[np.concatenate([x/d[:,h,None] for h in range(heads)],axis=1),
                     np.concatenate([-x*a[:,h,None]/d[:,h,None]**2 for h in range(heads)],axis=1)]
    source_record = dict(n=n, heads=heads, seed=args.seed, indices=indices.tolist(),
                         b_numerator=b_num.tolist(),u_numerator=u_num.tolist(),scale=10,
                         singular_values=np.linalg.svd(jac(source),compute_uv=False).tolist())
    (args.out/'source.json').write_text(json.dumps(source_record,indent=2)+'\n')
    print(json.dumps(dict(event='source',**source_record)),flush=True)
    lower=np.r_[np.full(heads*n,-1000.),np.full(heads*n,1.e-5)]
    upper=np.r_[np.full(heads*n,1000.),np.full(heads*n,100.)]
    candidates=[]
    start=time.monotonic()
    with (args.out/'search.jsonl').open('a') as stream:
        for j in range(args.starts):
            if j % 2:
                p0=source+np.r_[rng.normal(0,.3,heads*n),rng.normal(0,.15,heads*n)]
                p0=np.clip(p0,lower+1.e-6,upper-1.e-6)
            else:
                b=np.exp(rng.uniform(-2,2,(heads,n)))
                design=np.concatenate([x/(1+x@b[h])[:,None] for h in range(heads)],axis=1)
                u=np.linalg.lstsq(design,y,rcond=None)[0]
                p0=np.r_[np.clip(u,-999,999),b.ravel()]
            fit=least_squares(fun,p0,jac=jac,bounds=(lower,upper),max_nfev=6000,
                              ftol=1e-13,xtol=1e-13,gtol=1e-13)
            residual=float(np.max(np.abs(fun(fit.x))))
            global_difference=float(np.max(np.abs(evaluate(fit.x,cube)-evaluate(source,cube))))
            record=dict(start=j,seconds=time.monotonic()-start,nfev=fit.nfev,
                        residual=residual,global_difference=global_difference,
                        min_b=float(np.min(fit.x[heads*n:])),
                        min_singular=float(np.linalg.svd(jac(fit.x),compute_uv=False)[-1]))
            stream.write(json.dumps(record)+'\n');stream.flush()
            if residual<1.e-10 and global_difference>1.e-5:
                record['parameters']=fit.x.tolist()
                target=args.out/f'candidate-{j}.json'
                target.write_text(json.dumps(record,indent=2)+'\n')
                print(json.dumps(dict(event='candidate',file=str(target),**record)),flush=True)
                candidates.append(record)
                if len(candidates)>=10: break
            elif j%10==0:
                print(json.dumps(dict(event='progress',**record)),flush=True)
    print(json.dumps(dict(event='finished',candidates=len(candidates),seconds=time.monotonic()-start)),flush=True)

if __name__=='__main__':main()
