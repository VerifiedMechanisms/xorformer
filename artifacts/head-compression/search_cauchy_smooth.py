#!/usr/bin/env python3
"""Squared-hinge positive-pole decoder search with exact final auditing.

This numerical optimization is a finite promised-grid experiment, with no
convergence or universal representability claim. Run through heavy.
"""
import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import time
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[key]='1'
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
from flint import arb,arb_mat
from search_cauchy_arb import grid_basis
from refit_high_precision import exact_midpoint,rational_ball
from search_varpro_scores import convex_hinge_fit
from verify_cauchy_grid import verify


class Finished(Exception):pass


def fit(logs,sigma,labels,bits):
    m,k=labels.shape;h=len(logs);y=labels.ravel()
    penalty=1e-5
    b=[Fraction(float(t)) for t in np.exp(logs)]
    f,inverse,q,r,bb=grid_basis(b,sigma,m,bits)
    result=convex_hinge_fit(y[:,None]*q,q.T@y,'newton',penalty)
    preliminary=y*(q@result.x)
    active=np.flatnonzero(preliminary<1)
    gram=f.transpose()*f
    for iteration in range(20):
        fa=arb_mat([[f[i,t] for t in range(h)] for i in active])
        ya=arb_mat([[int(y[i])] for i in active])
        a=(fa.transpose()*fa+rational_ball(penalty)*gram).solve(fa.transpose()*ya)
        scores=f*a
        margins=np.array([int(y[i])*float(scores[i,0].mid()) for i in range(m*k)])
        new_active=np.flatnonzero(margins<1)
        if np.array_equal(active,new_active):break
        active=new_active
    else:raise ArithmeticError('regularized active-set iteration did not settle')
    scores=f*a
    margins=np.array([int(y[i])*float(scores[i,0].mid()) for i in range(m*k)])
    residual=np.maximum(1-margins,0)
    active_set=set(active.tolist())
    if (any(margins[i]>1+1e-7 for i in active) or
        any(margins[i]<1-1e-7 for i in range(m*k) if i not in active_set)):
        raise ArithmeticError('squared-hinge active-set refit is inconsistent: '+str({
            'active':len(active),'dimension':h,'max_active':float(margins[active].max()),
            'min_inactive':float(min((margins[i] for i in range(m*k) if i not in active_set),default=2)),
            'preliminary_loss':float(np.maximum(1-preliminary,0)@np.maximum(1-preliminary,0)/2/(m*k)),
            'refit_loss':float(residual@residual/2/(m*k))}))
    gradient=[]
    for t in range(h):
        value=sum((((scores[i,0]-int(y[i]) if i in active_set else arb(0))+
                    rational_ball(penalty)*scores[i,0])*a[t,0]*f[i,t]*
            ((i//k+1)-bb[t])/((i//k+1)+bb[t]) for i in range(m*k)),arb(0))
        gradient.append(float(value.mid())/(m*k))
    return .5*float(residual@residual+penalty*(margins@margins))/(m*k),np.array(gradient),a,b,margins,float(la.norm(result.jac,np.inf))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--checkpoint',type=Path,required=True)
    parser.add_argument('--seconds',type=float,default=16200)
    parser.add_argument('--bits',type=int,default=1024)
    parser.add_argument('--gradient-check',action='store_true')
    args=parser.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    saved=np.load(args.checkpoint);sigma=saved['sigma'];labels=saved['labels'];initial=saved['logs']
    m,k=labels.shape;h=len(initial);start=time.monotonic();best=float('inf');evaluations=0
    rng=np.random.default_rng(260000+k)
    if args.gradient_check:
        loss,g,*rest=fit(initial,sigma,labels,args.bits)
        direction=rng.normal(size=h);direction/=la.norm(direction)
        eps=1e-5
        fd=(fit(initial+eps*direction,sigma,labels,args.bits)[0]-
            fit(initial-eps*direction,sigma,labels,args.bits)[0])/(2*eps)
        print(json.dumps({'loss':loss,'analytic':float(g@direction),'finite_difference':fd,
            'inner_gradient':rest[-1]}));return
    def objective(logs):
        nonlocal best,evaluations
        if time.monotonic()-start>=args.seconds:raise Finished
        loss,g,a,b,margins,inner=fit(logs,sigma,labels,args.bits);evaluations+=1
        if loss<best:
            best=loss
            np.savez(args.out/'checkpoint.npz',logs=logs,labels=labels,sigma=sigma)
            print(json.dumps({'seconds':time.monotonic()-start,'evaluations':evaluations,
                'loss':loss,'errors':int((margins<=0).sum()),'inner_gradient':inner}),flush=True)
        if margins.min()>1e-6:
            aa=[exact_midpoint(a[t,0]) for t in range(h)]
            exact=[int(labels[p-1,j])*sum((4*aa[t]*b[t]*int(sigma[t,j])/(p+b[t])**2
                for t in range(h)),Fraction(0)) for p in range(1,m+1) for j in range(k)]
            if min(exact)<=0:raise ArithmeticError('exact sign audit failed')
            margin=min(exact);path=args.out/'certificate.json'
            path.write_text(json.dumps({'a':[[v.numerator,v.denominator] for v in aa],
                'b':[[v.numerator,v.denominator] for v in b],'labels':labels.tolist(),
                'sigma':sigma.tolist(),'margin':[margin.numerator,margin.denominator],
                'scope':'Finite promised-grid signs only.'})+'\n')
            print(json.dumps(verify(path)),flush=True);raise Finished
        return loss,g
    restart=0
    while time.monotonic()-start<args.seconds:
        try:
            opt.minimize(objective,initial,jac=True,method='L-BFGS-B',
                bounds=[(-8,np.log(m)+8)]*h,
                options={'maxiter':2000,'maxls':30,'gtol':1e-10,'ftol':1e-14})
        except ArithmeticError as e:
            print(json.dumps({'restart':restart,'rejected':str(e)}),flush=True)
        except Finished:break
        restart+=1
        best_path=args.out/'checkpoint.npz'
        if best_path.exists() and restart%4:
            initial=np.load(best_path)['logs']+rng.normal(0,.05,h)
        else:initial=rng.uniform(-4,np.log(m)+4,h)
    print(json.dumps({'seconds':time.monotonic()-start,'best_loss':best,
        'evaluations':evaluations,'target_proved':False}),flush=True)


if __name__=='__main__':main()
