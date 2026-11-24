#!/usr/bin/env python3
"""Random-restart hinge continuation followed by full-cube margin LP refinement."""
import argparse
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import minimize
from search_joint_relative_margin import MarginLP,cube

p=argparse.ArgumentParser();p.add_argument('--input',required=True);p.add_argument('--index',type=int,required=True)
p.add_argument('--restarts',type=int,default=100);p.add_argument('--seed',type=int,default=213)
p.add_argument('--output',required=True);a=p.parse_args()
d=json.loads(Path(a.input).read_text()); row=d['results'][a.index];n=d['config']['n'];H=d['config']['heads']
x=cube(n);labels=[1 if ch=='+' else -1 for ch in row['labels']];rng=np.random.default_rng(a.seed)
best=row['best'];runs=[];beg=time.time()
for j in range(a.restarts):
    orientation=rng.choice([-1,1],H)
    start=np.clip(rng.normal(0,[.3,1,3][j%3],H*(n+1)),-6,6)
    goal=[.02,.05,.1,.2][j%4]
    hinge=MarginLP(x,labels,H,orientation,goal)
    try:
        hop=minimize(hinge.solve,start,method='L-BFGS-B',jac=True,bounds=[(-6,6)]*len(start),
                     options={'maxiter':100,'ftol':1e-11,'gtol':1e-8,'maxls':30})
        lp=MarginLP(x,labels,H,orientation)
        opt=minimize(lp.solve,hop.x,method='L-BFGS-B',jac=True,bounds=[(-6,6)]*len(start),
                     options={'maxiter':120,'ftol':1e-12,'gtol':1e-8,'maxls':30})
        check=lp.solve(opt.x,True);check['theta']=opt.x.tolist()
        runs.append({'restart':j,'margin':check['checked_margin'],'hinge':float(hop.fun),
                     'hinge_goal':goal,'calls':lp.calls+hinge.calls})
        if check['checked_margin']>best['checked_margin']:best=check
    except RuntimeError as ex:
        runs.append({'restart':j,'error':str(ex)})
    out={'status':'numerical lower certificates, no global optimality claim','source':a.input,
         'source_index':a.index,'labels':row['labels'],'n':n,'heads':H,
         'best':best,'runs':runs,'elapsed_seconds':time.time()-beg}
    Path(a.output).write_text(json.dumps(out,indent=2)+'\n')
    if j%10==0:print(json.dumps({'restart':j,'best_margin':best['checked_margin'],'seconds':time.time()-beg}),flush=True)
