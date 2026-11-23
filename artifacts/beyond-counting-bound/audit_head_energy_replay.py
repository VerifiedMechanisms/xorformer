"""Numerical first- and second-order diagnostics for a saved energy replay.

Neither these finite differences nor the least-squares multipliers are an
interval certificate. Run via heavy on a shared machine.
"""
import argparse,json
from pathlib import Path
import numpy as np
from scipy.optimize import nnls
from scipy.linalg import null_space
from search_head_energy_minima import evaluate

p=argparse.ArgumentParser();p.add_argument('replay',type=Path);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();r=json.loads(a.replay.read_text());t=np.array(r['theta']);n,h=r['n'],r['heads']
x=((np.arange(2**n)[:,None]>>np.arange(n))&1).astype(float)
y=np.array(r['labels']);ori=np.array(r['orientation']);active=np.array(r['active_vertices'])
v,j,e,g=evaluate(t,x,n,h,ori);signed=y[active,None]*j[active]
dual,res=nnls(signed.T,g,maxiter=100000);basis=null_space(signed,rcond=1e-9)
def grad(z):
    _,jj,_,gg=evaluate(z,x,n,h,ori)
    return gg-jj[active].T@(y[active]*dual)
curv=[]
for step in [1e-4,1e-5,1e-6]:
    mat=np.column_stack([(grad(t+step*np.eye(len(t))[i])-grad(t-step*np.eye(len(t))[i]))/(2*step) for i in range(len(t))])
    ev=np.linalg.eigvalsh(basis.T@((mat+mat.T)/2)@basis)
    curv.append(dict(step=step,min_eigenvalue=float(ev[0]),max_eigenvalue=float(ev[-1]),
        hessian_asymmetry=float(np.max(abs(mat-mat.T)))))
out=dict(status='NUMERICAL_REPLAY_NOT_CERTIFICATE',
    relative_stationarity_residual=float(res/max(1,np.linalg.norm(g))),
    minimum_multiplier=float(dual.min()),positive_multipliers=int(sum(dual>1e-7)),
    active_rank_min_singular=float(np.linalg.svd(signed,compute_uv=False)[-1]),
    tangent_dimension=basis.shape[1],curvature=curv,main_target_proved=False)
a.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
