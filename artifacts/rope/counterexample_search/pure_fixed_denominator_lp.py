"""Exact-shape linear feasibility for pure heads with fixed denominators.

For each sign of k, u=k*s+ell*beta, abs(beta)<s and sum(s)<1
becomes a strict polyhedral system in (u,ell,abs(k)). This avoids fitting
the token values and positive masses by a nonlinear optimizer.
Floating LP success still requires exact rational verification.
"""
import argparse
import itertools
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import linprog

from search_g12_pure_three import data


def pure_lp(z,y,beta,signs):
    h,n=beta.shape
    dim=1+h*n+2*h
    den=1+z@beta.T
    assert np.min(den)>0
    features=np.column_stack([np.ones(len(z))]+[z/den[:,j,None] for j in range(h)]+[np.zeros((len(z),2*h))])
    rows=[-y[:,None]*features]
    rhs=[-np.ones(len(z))]
    for j in range(h):
        e=signs[j]
        for i in range(n):
            # e*u_i-e*ell*beta_i-K*abs(beta_i) >= 1.
            row=np.zeros(dim)
            row[1+j*n+i]=-e
            row[1+h*n+j]=e*beta[j,i]
            row[1+h*n+h+j]=abs(beta[j,i])
            rows.append(row[None,:]);rhs.append(np.array([-1.]))
        # K-sum(e*u_i-e*ell*beta_i) >= 1.
        row=np.zeros(dim)
        row[1+j*n:1+(j+1)*n]=e
        row[1+h*n+j]=-e*sum(beta[j])
        row[1+h*n+h+j]=-1
        rows.append(row[None,:]);rhs.append(np.array([-1.]))
    lp=linprog(np.zeros(dim),A_ub=np.vstack(rows),b_ub=np.concatenate(rhs),bounds=[(None,None)]*dim,method='highs')
    return lp


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--target',choices=['g12','f7xor'],default='f7xor')
    ap.add_argument('--samples',type=int,default=1000)
    ap.add_argument('--seed',type=int,default=101010)
    ap.add_argument('--out',default='/tmp/pure_fixed_lp.jsonl')
    args=ap.parse_args()
    z,y=data(args.target); n=z.shape[1];h=3;rng=np.random.default_rng(args.seed)
    start=time.time()
    for j in range(args.samples):
        ints=rng.integers(-100,101,(h,n))
        if j%3==0:
            # Separate the x, y and query-sign blocks in the initial poles.
            ints[:]=0
            ints[0,:4]=rng.integers(-100,101,4)
            ints[1,4:7]=rng.integers(-100,101,3)
            ints[2,7]=rng.integers(-100,101)
            ints+=rng.integers(-5,6,(h,n))
        scales=np.sum(abs(ints),axis=1)+rng.integers(1,50,h)
        beta=ints/scales[:,None]
        for signs in itertools.product([-1,1],repeat=h):
            lp=pure_lp(z,y,beta,signs)
            if lp.success:
                out={'target':args.target,'sample':j,'seed':args.seed,'beta_ints':ints.tolist(),'beta_scales':scales.tolist(),'signs':signs,'solution':lp.x.tolist()}
                Path(args.out).write_text(json.dumps(out)+'\n')
                print('FLOATING LP FEASIBLE; exact verification still required',out,flush=True)
                return
        if j%25==0:
            print(j,'inconclusive',round(time.time()-start,2),flush=True)
    print('No floating feasible fixed-denominator system. This is not a lower bound.',flush=True)


if __name__=='__main__':
    main()
