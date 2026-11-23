"""Exact mixed binary fibers of positive affine-ratio scores.

Zero residuals and ranks are computed in integers and modulo a checked prime.
The signed-multiplier linear program is exploratory only. No asymptotic head
lower bound, full-cube margin theorem, or impossibility inference is made.
Run through heavy on the shared machine.
"""
import argparse
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import linprog
from search_integer_zero_fibers import PRIME, subset_sums, rank_and_pivots


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--seconds', type=float, default=7200)
    p.add_argument('--seed', type=int, default=8930701)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    assert all(PRIME % k for k in range(2, int(PRIME**0.5)+1))
    rng = np.random.default_rng(args.seed)
    started = time.monotonic()
    best = {}
    trial = 0
    with (args.output/'results.jsonl').open('a', buffering=1) as log:
        while time.monotonic()-started < args.seconds:
            n,h = [(16,3),(18,3),(20,3)][trial%3]
            b = rng.integers(1,5,size=(h,n),dtype=np.int64)
            mode = (trial//3)%4
            U = -b + rng.integers(-3-3*mode,4+3*mode,size=(h,n),dtype=np.int64)
            den = 1+subset_sums(b)
            num = subset_sums(U)
            product = np.prod(den,axis=1)
            rnum = np.sum(num*(product[:,None]//den),axis=1)
            positive = np.flatnonzero(rnum==0)
            positive = positive[positive!=0]
            negative = np.flatnonzero(rnum==-2*h*product)
            record = dict(trial=trial,n=n,heads=h,positive=len(positive),negative=len(negative),
                          elapsed_seconds=time.monotonic()-started,status='UNKNOWN')
            if len(positive) and len(negative) and len(positive)+len(negative)>=2*n*h:
                # Positive rows first ensures a retained basis has a positive row.
                positive = rng.permutation(positive)[:4*n*h]
                negative = rng.permutation(negative)[:4*n*h]
                sample = np.r_[positive,negative]
                labels = np.r_[np.ones(len(positive)), -np.ones(len(negative))]
                x = ((sample[:,None]>>np.arange(n))&1).astype(np.int64)
                d = den[sample]
                iv = np.array([[pow(int(v),-1,PRIME) for v in row] for row in d],dtype=np.int64)
                av = num[sample]*pow(h,-1,PRIME)%PRIME
                ju = (x[:,None,:]*iv[:,:,None]).reshape(len(x),-1)
                sc = av*iv%PRIME*iv%PRIME
                jb = (-x[:,None,:]*sc[:,:,None]).reshape(len(x),-1)
                rank,rows,cols=rank_and_pivots(np.c_[ju,jb]%PRIME)
                selected_labels=labels[rows]
                record.update(certified_rank=rank,selected_positive=int(sum(selected_labels>0)),
                              selected_negative=int(sum(selected_labels<0)))
                if rank==2*n*h and np.any(selected_labels>0) and np.any(selected_labels<0):
                    record['status']='EXACT_MIXED_BINARY_RANK'
                    # A float LP is not a dual certificate.
                    juf=(x[:,None,:]/d[:,:,None]).reshape(len(x),-1)
                    jbf=(-x[:,None,:]*(num[sample]/h/d**2)[:,:,None]).reshape(len(x),-1)
                    jac=np.c_[juf,jbf]
                    gradient=np.r_[2*U.ravel()/h,np.zeros(n*h)]
                    dual=linprog(np.ones(len(sample)),A_eq=(labels[:,None]*jac).T,
                        b_eq=gradient,bounds=(0,None),method='highs')
                    record['float_nonnegative_dual_lp']=int(dual.status)
                    full_num=h*product+rnum
                    record['full_cube_unit_margin_violations']=int(np.count_nonzero(abs(full_num)<h*product))
                    key=(n,h)
                    if key not in best or dual.status==0:
                        cert=dict(record,denominator_slopes=b.tolist(),numerator_scaled_slopes=U.tolist(),
                            numerator_scale=h,prime=PRIME,
                            sample_indices=[int(sample[i]) for i in rows],
                            labels=[int(labels[i]) for i in rows],parameter_columns=cols,
                            all_test_indices=sample.tolist(),all_test_labels=labels.tolist(),
                            floating_dual=dual.x.tolist() if dual.status==0 else None,
                            scope='finite exact binary rank only; LP not certified; main target unproved')
                        name=f'n{n}-h{h}-trial{trial}.json'
                        (args.output/name).write_text(json.dumps(cert,indent=2)+'\n')
                        record['certificate']=name
                        best[key]=name
            if 'certified_rank' in record or trial%30==0:
                log.write(json.dumps(record)+'\n')
                print(json.dumps(record),flush=True)
            trial+=1
    print(json.dumps(dict(status='SEARCH_FINISHED_UNKNOWN',trials=trial,
        elapsed_seconds=time.monotonic()-started,certificates={str(k):v for k,v in best.items()},
        target_proved=False)),flush=True)


if __name__=='__main__':
    main()
