#!/usr/bin/env python3
"""Exploratory finite LP tests, never a lower-bound proof.

Retain A_h and B_h directions, allow head-specific exponential scales and
independent scalar weights for powers 1..K, plus a free bias.
"""
import argparse, itertools, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--n',type=int,default=7)
    ap.add_argument('--heads',type=int,default=2)
    ap.add_argument('--trials',type=int,default=30)
    ap.add_argument('--seed',type=int,default=912)
    ap.add_argument('--out',required=True)
    args=ap.parse_args()
    rng=np.random.default_rng(args.seed)
    X=np.array(list(itertools.product([0.,1.],repeat=args.n)))
    Y=np.c_[np.ones(len(X)),X]
    records=[]
    started=time.time()
    for trial in range(args.trials):
        # Include broad but finite scale separation, with both orientations.
        scale = 2. if trial%3==0 else (8. if trial%3==1 else 25.)
        bc=np.exp(rng.uniform(-scale,scale,size=(args.heads,args.n+1)))
        B=Y@bc.T
        for h in range(args.heads):
            if rng.integers(2):
                B[:,h]=bc[h,0]+(1-X)@bc[h,1:]
        ac=rng.normal(size=(args.heads,args.n+1))
        A=Y@ac.T
        raw=np.sum(A/B,axis=1)
        c=-float(np.median(raw))
        score=raw+c
        F=np.where(score>0,1.,-1.)
        base=1/np.median(B,axis=0)
        # Head-specific scales, not one globally shared grid.
        factors=(.03,.15,.75,3.,15.,75.)
        fits=[]
        for K in (1,2,3,args.n):
            success=None
            for fac in itertools.product(factors,repeat=args.heads):
                taus=base*np.array(fac)
                cols=[np.ones(len(X))]
                for h in range(args.heads):
                    z=np.exp(-taus[h]*B[:,h])
                    width=float(np.max(z)-np.min(z))
                    zz=2*(z-np.min(z))/width-1 if width>0 else z
                    # This spans powers 0..K but improves floating conditioning.
                    expo=np.polynomial.chebyshev.chebvander(zz,K)
                    for j in range(K+1):
                        v=A[:,h]*expo[:,j]
                        norm=np.max(np.abs(v))
                        cols.append(v/norm if norm else v)
                M=np.array(cols).T
                result=linprog(np.zeros(M.shape[1]),A_ub=-F[:,None]*M,b_ub=-np.ones(len(X)),bounds=[(None,None)]*M.shape[1],method='highs')
                if result.success and np.min(F*(M@result.x))>.99:
                    success={'factors':fac,'minimum_computed_margin':float(np.min(F*(M@result.x)))}
                    break
            fits.append({'K':K,'found':success})
            if success and K==1:
                break
        records.append({'trial':trial,'range_scale':scale,'minimum_original_abs_score':float(np.min(np.abs(score))),'positive_labels':int(np.sum(F>0)),'fits':fits})
        print(json.dumps(records[-1]),flush=True)
        if not any(rec['found'] for rec in fits):
            records[-1]['failed_instance_tables']={'A':A.tolist(),'B':B.tolist(),'bias':c,'labels':F.astype(int).tolist()}
    out={'status':'exploratory floating-point LP, failure is not impossibility','n':args.n,'heads':args.heads,'seed':args.seed,'elapsed_seconds':time.time()-started,'records':records}
    Path(args.out).write_text(json.dumps(out,indent=2))

if __name__=='__main__':main()
