#!/usr/bin/env python3
"""Numerical simultaneous denominator-boundary/refit exploration.

Every objective evaluation solves the full-cube numerator and head-norm LP.
SLSQP moves all denominator coefficients together on a product of simplices.
Zero slopes are allowed in this comparison closure, and a strictly positive
gap at such a point persists after small positive-slope perturbations. This
script gives witnesses only, never global optimality or failure certificates.
"""
import argparse
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import minimize
from search_joint_relative_margin import MarginLP, cube


class BoundaryLP(MarginLP):
    def solve_weights(self, weights, details=False):
        w = np.reshape(weights, (self.h, self.d))
        # The existing solver's softmax gives the exact prescribed positive
        # weights. A tiny floor only regularizes the numerical zero boundary.
        safe = np.maximum(w, 1e-14)
        theta = np.log(safe)
        if details:
            ans = super().solve(theta.ravel(), True)
            ans['boundary_weights'] = w.tolist()
            ans['active_slopes'] = [int(np.sum(row[1:] > 1e-7)) for row in w]
            return ans
        value, log_gradient = super().solve(theta.ravel(), False)
        # The simplex tangent derivative is log-gradient / weight. Its missing
        # head-wise constant vanishes on each simplex tangent space.
        gradient = np.reshape(log_gradient, w.shape) / safe
        return value, gradient.ravel()


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--input', required=True)
    p.add_argument('--output', required=True)
    p.add_argument('--restarts', type=int, default=3)
    p.add_argument('--iterations', type=int, default=120)
    p.add_argument('--seed', type=int, default=4211)
    p.add_argument('--limit', type=int, default=10000)
    p.add_argument('--force-slopes', type=int, default=0,
                   help='Number of slope coordinates fixed to zero in each head')
    args=p.parse_args()
    data=json.loads(Path(args.input).read_text())
    n=data['config']['n']; h=data['config']['heads']; d=n+1
    x=cube(n); rng=np.random.default_rng(args.seed); out=[]; starttime=time.time()
    for target in data['results'][:args.limit]:
        labels=np.array([1 if v=='+' else -1 for v in target['labels']])
        results=[]
        for run in range(args.restarts):
            orientation=np.array(target['best']['orientation']) if run==0 else rng.choice([-1,1],h)
            w=np.array(target['best']['weights']) if run==0 else rng.dirichlet(np.ones(d),h)
            mask=np.zeros((h,d),dtype=bool)
            for head in range(h):
                zeros=(np.argsort(w[head,1:])[:args.force_slopes]+1 if run==0 else
                       rng.choice(np.arange(1,d),args.force_slopes,replace=False))
                mask[head,zeros]=True
            w[mask]=0
            w/=w.sum(axis=1)[:,None]
            lp=BoundaryLP(x,labels,h,orientation)
            initial=lp.solve_weights(w.ravel(),True)
            cons={'type':'eq','fun':lambda v:np.reshape(v,(h,d)).sum(axis=1)-1,
                  'jac':lambda v:np.kron(np.eye(h),np.ones((1,d)))}
            bounds=[((0,0) if mask[head,j] else ((1e-7,1) if j==0 else (0,1)))
                    for head in range(h) for j in range(d)]
            try:
                opt=minimize(lp.solve_weights,w.ravel(),jac=True,method='SLSQP',
                             constraints=[cons],bounds=bounds,
                             options={'maxiter':args.iterations,'ftol':1e-10})
                result=lp.solve_weights(opt.x,True)
                result.update(success=bool(opt.success),message=str(opt.message),iterations=int(opt.nit))
            except RuntimeError as e:
                result=initial;result.update(success=False,message=str(e),iterations=0)
            result['initial_margin']=initial['checked_margin']
            results.append(result)
        best=max(results,key=lambda r:r['checked_margin'])
        summaries=[{k:r[k] for k in ['checked_margin','initial_margin','active_slopes',
                                      'success','message','iterations']} for r in results]
        out.append({'index':target['index'],'labels':target['labels'],
                    'prior_margin':target['best']['checked_margin'],'best':best,'runs':summaries})
        output={'status':'numerical witnesses only; no global optimization claims',
                'config':vars(args),'n':n,'heads':h,'elapsed_seconds':time.time()-starttime,'results':out}
        Path(args.output).write_text(json.dumps(output,indent=2)+'\n')
        print(json.dumps({'index':target['index'],'prior':target['best']['checked_margin'],
                          'margin':best['checked_margin'],'active_slopes':best['active_slopes'],
                          'seconds':time.time()-starttime}),flush=True)


if __name__=='__main__': main()
