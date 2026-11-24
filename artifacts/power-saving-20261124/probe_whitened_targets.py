#!/usr/bin/env python3
"""Variable-projection search allowing large cancelling numerator coefficients.

The QR span is only a numerical exploration device. Every successful witness
needs a separate exact-rational audit. Numerical misses prove nothing.
"""
import argparse,json,time
from pathlib import Path
from datetime import datetime,timezone
import numpy as np
import torch
from scipy.optimize import minimize,linprog


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--n',type=int,required=True)
    ap.add_argument('--heads',type=int,required=True)
    ap.add_argument('--samples',type=int,default=8)
    ap.add_argument('--restarts',type=int,default=10)
    ap.add_argument('--steps',type=int,default=300)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--seed',type=int,default=20261124)
    ar=ap.parse_args(); n,H=ar.n,ar.heads
    torch.set_num_threads(1);torch.set_default_dtype(torch.float64)
    rng=np.random.default_rng(ar.seed)
    cube=((np.arange(2**n)[:,None]>>np.arange(n))&1).astype(float)
    X=torch.tensor(cube);N=len(X)
    orientations=np.where(np.arange(H)%2,-1,1)
    inp=torch.stack([X if o==1 else 1-X for o in orientations])
    report={'started_utc':datetime.now(timezone.utc).isoformat(),
      'status':'numerical only, no impossibility conclusions',
      'n':n,'heads':H,'orientations':orientations.tolist(),'results':[]}
    start=time.monotonic()
    for sample in range(ar.samples):
        yy=rng.choice([-1.,1.],N); y=torch.tensor(yy)
        rec={'sample':sample,'labels':yy.astype(int).tolist(),'runs':[]}
        best=1.;success=None
        for restart in range(ar.restarts):
            b0=rng.normal(0,2,(H,n));inner_w=np.zeros(1+n*H)
            evals=0; best_local=1.; bestdata=None
            def obj(flat):
                nonlocal inner_w,evals,best,best_local,bestdata,success
                logb=torch.tensor(flat.reshape(H,n),requires_grad=True)
                slopes=torch.nn.functional.softplus(logb)
                B=1+torch.einsum('hvi,hi->hv',inp,slopes)
                M=torch.cat([torch.ones((N,1))]+[X/B[h,:,None] for h in range(H)],dim=1)
                Q,R=torch.linalg.qr(M,mode='reduced'); q=Q.detach().numpy()
                def inner(w):
                    d=np.minimum(yy*(q@w)-1,0)
                    return float(d@d/N),2*q.T@(yy*d)/N
                innerres=minimize(inner,inner_w,jac=True,method='L-BFGS-B',
                      options={'maxiter':200,'ftol':1e-13,'gtol':1e-9,'maxls':30})
                inner_w=innerres.x
                s=Q@torch.tensor(inner_w)
                loss=torch.relu(1-y*s).square().mean()
                loss.backward();grad=logb.grad.detach().numpy().ravel()
                err=float((y*s<=0).double().mean());evals+=1
                if err<best_local:
                    best_local=err;best=min(best,err)
                    cc=torch.linalg.solve_triangular(R,torch.tensor(inner_w)[:,None],upper=True)[:,0]
                    direct=(M@cc).detach().numpy()
                    bestdata={'slopes':slopes.detach().numpy().tolist(),
                              'coefficients':cc.detach().numpy().tolist(),
                              'qr_error':err,'direct_margin':float(np.min(yy*direct)),
                              'condition':float(torch.linalg.cond(R))}
                    if np.min(yy*direct)>1e-6:success=bestdata
                return float(loss),grad
            out=minimize(obj,b0.ravel(),jac=True,method='L-BFGS-B',
                options={'maxiter':ar.steps,'maxls':30,'ftol':1e-12,'gtol':1e-9})
            rec['runs'].append({'restart':restart,'error':best_local,'loss':float(out.fun),
                 'evals':evals,'message':str(out.message),'best':bestdata})
            print(json.dumps({'sample':sample,'restart':restart,'best_error':best,
                              'success':success is not None,'elapsed':time.monotonic()-start}),flush=True)
            if success is not None:
                rec['witness']=success;break
        report['results'].append(rec)
        report['elapsed_seconds']=time.monotonic()-start
        report['checkpoint_utc']=datetime.now(timezone.utc).isoformat()
        ar.out.write_text(json.dumps(report,indent=2)+'\n')
    report['finished_utc']=datetime.now(timezone.utc).isoformat()
    ar.out.write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
