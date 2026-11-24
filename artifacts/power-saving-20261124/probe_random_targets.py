#!/usr/bin/env python3
"""Numerical search in the original positive/negative denominator model.

Success records only floating-point witnesses until exact rational validation.
Failure is not an impossibility result. Conditioning and coefficient sizes are
unrestricted in the model, and this finite optimizer need not discover them.
"""
import argparse
import json
from pathlib import Path
import time
from datetime import datetime, timezone
import numpy as np
import torch
from scipy.optimize import linprog


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--n',type=int,required=True)
    ap.add_argument('--heads',type=int,required=True)
    ap.add_argument('--samples',type=int,default=10)
    ap.add_argument('--restarts',type=int,default=12)
    ap.add_argument('--steps',type=int,default=1000)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--seed',type=int,default=20261124)
    ar=ap.parse_args()
    torch.set_num_threads(1)
    torch.set_default_dtype(torch.float64)
    rng=np.random.default_rng(ar.seed)
    n,H=ar.n,ar.heads
    cube=((np.arange(2**n)[:,None]>>np.arange(n))&1).astype(float)
    X=torch.tensor(cube)
    F=torch.cat([torch.ones((len(X),1)),X],dim=1)
    orientations=np.where(np.arange(H)%2, -1,1)
    inputs=torch.stack([X if o==1 else 1-X for o in orientations],dim=0)
    report={'started_utc':datetime.now(timezone.utc).isoformat(),
      'n':n,'heads':H,'seed':ar.seed,'status':'numerical experiment only',
      'orientations':orientations.tolist(),'results':[]}
    start=time.monotonic()
    for sample in range(ar.samples):
        yy=rng.choice([-1.,1.],len(X)); y=torch.tensor(yy)
        best=1.; result={'sample':sample,'labels':yy.astype(int).tolist(),'runs':[]}
        for restart in range(ar.restarts):
            # Gauge each denominator at its monotone minimizing corner to 1.
            # Slopes are strictly positive; orientation handles negative heads.
            logb=torch.tensor(rng.normal(-1,2,(H,n)),requires_grad=True)
            coeff=torch.tensor(rng.normal(0,.05,(H,n+1)),requires_grad=True)
            bias=torch.tensor(0.,requires_grad=True)
            opt=torch.optim.LBFGS([logb,coeff,bias],lr=.8,max_iter=20,
                                  line_search_fn='strong_wolfe',tolerance_grad=1e-10,
                                  tolerance_change=1e-12)
            for step in range((ar.steps+19)//20):
                def closure():
                    opt.zero_grad()
                    B=1+torch.einsum('hvi,hi->hv',inputs,torch.nn.functional.softplus(logb))
                    s=bias+((coeff@F.T)/B).sum(0)
                    loss=torch.relu(1-y*s).square().mean()
                    if torch.isfinite(loss): loss.backward()
                    return loss
                try:
                    loss=opt.step(closure)
                except (IndexError, RuntimeError) as exc:
                    print(json.dumps({"optimizer_interruption":str(exc),"sample":sample,"restart":restart}),flush=True)
                    break
                if not torch.isfinite(loss): break
                if step%5==0 or step==(ar.steps+19)//20-1:
                    with torch.no_grad():
                        slopes=torch.nn.functional.softplus(logb).numpy()
                        B=1+np.einsum('hvi,hi->hv',inputs.numpy(),slopes)
                        # Test the entire affine numerator span at these poles.
                        M=np.column_stack([np.ones(len(X))]+[cube/B[h,:,None] for h in range(H)])
                        lp=linprog(np.zeros(M.shape[1]),A_ub=-yy[:,None]*M,
                                   b_ub=-np.ones(len(X)),bounds=[(None,None)]*M.shape[1],
                                   method='highs')
                        if lp.success and np.min(yy*(M@lp.x))>.99:
                            result['witness']={'slopes':slopes.tolist(),'coefficients':lp.x.tolist(),
                                               'margin':float(np.min(yy*(M@lp.x)))}
                            break
            with torch.no_grad():
                B=1+torch.einsum('hvi,hi->hv',inputs,torch.nn.functional.softplus(logb))
                s=bias+((coeff@F.T)/B).sum(0)
                error=float((y*s<=0).double().mean())
                best=min(best,error)
                run={'restart':restart,'errors':int((y*s<=0).sum()),
                     'loss':float(torch.relu(1-y*s).square().mean()),
                     'min_margin':float((y*s).min())}
                result['runs'].append(run)
            print(json.dumps({'sample':sample,'restart':restart,'best_error':best,
                    'witness':'witness' in result,'elapsed':time.monotonic()-start}),flush=True)
            if 'witness' in result:break
        result['best_error']=best
        result['best_error_scope']='optimizer score before the separate affine-span LP'
        if 'witness' in result: result['post_lp_error']=0
        report['results'].append(result)
        report['elapsed_seconds']=time.monotonic()-start
        report['checkpoint_utc']=datetime.now(timezone.utc).isoformat()
        ar.out.write_text(json.dumps(report,indent=2)+'\n')
    report['finished_utc']=datetime.now(timezone.utc).isoformat()
    ar.out.write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
