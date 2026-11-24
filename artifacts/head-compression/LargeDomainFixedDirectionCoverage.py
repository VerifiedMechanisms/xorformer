#!/usr/bin/env python3
"""Numerical sign-coverage exploration; run with heavy, never a proof.

For each sampled offset vector, enumerate the chambers of the central feature
arrangement by its codimension-one vertices. Genericity and floating point
are not certified. Every reported pattern is re-evaluated at a concrete
floating-point coefficient vector; a full result still requires exact proof.
"""
import argparse
import itertools
import json
import time
import numpy as np


def coverage(features, subsets, signs):
    # Whitening avoids losses from the almost coincident reciprocal columns.
    u, sing, vt = np.linalg.svd(features, full_matrices=False)
    if sing[-1] < 1e-15 * sing[0]:
        return np.array([], dtype=np.uint64), float(sing[0]/sing[-1]), 0
    q = u
    z = q[subsets]
    uu, ss, vv = np.linalg.svd(z, full_matrices=True)
    regular = ss[:, -1] > 1e-11
    z, vv, subsets = z[regular], vv[regular], subsets[regular]
    nulls = vv[:, -1, :]
    base = nulls @ q.T
    mask = np.ones(base.shape, dtype=bool)
    np.put_along_axis(mask, subsets, False, axis=1)
    margins = np.min(np.where(mask, np.abs(base), np.inf), axis=1)
    regular = margins > 1e-10
    z, vv, subsets, nulls, base, mask, margins = [v[regular] for v in
        (z, vv, subsets, nulls, base, mask, margins)]
    inv = np.linalg.pinv(z)
    perturb = np.einsum('bdh,sh->bsd', inv, signs)
    changes = np.einsum('bsd,nd->bsn', perturb, q)
    delta = margins[:, None] / (3*np.maximum(1, np.max(np.abs(changes), axis=2)))
    values = base[:,None,:] + delta[:,:,None] * changes
    # Only accept signs whose numerical margins are comfortably nonzero.
    valid = np.min(np.abs(values), axis=2) > 1e-12
    bitweights = np.left_shift(np.uint64(1), np.arange(q.shape[0],dtype=np.uint64))
    patterns = np.sum((values>0).astype(np.uint64)*bitweights,axis=2)[valid]
    fullmask = (1 << q.shape[0])-1
    return np.unique(np.minimum(patterns, fullmask-patterns)), float(sing[0]/sing[-1]), len(subsets)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--dimension',type=int,default=4)
    p.add_argument('--heads',type=int,default=4)
    p.add_argument('--samples',type=int,default=100)
    p.add_argument('--epsilon',type=float,default=.001)
    p.add_argument('--seed',type=int,default=2411)
    p.add_argument('--output')
    args=p.parse_args()
    rng=np.random.default_rng(args.seed)
    bits=np.array(list(itertools.product((0,1),repeat=args.dimension)))
    # Keep directions fixed across ALL offsets and target labelings.
    d=1+args.epsilon*rng.uniform(-1,1,(args.heads,args.dimension))
    subsets=np.array(list(itertools.combinations(range(len(bits)),args.heads)))
    signs=np.array(list(itertools.product((-1,1),repeat=args.heads)))
    seen=np.zeros(1 << (len(bits)-1),dtype=bool)
    t=time.monotonic()
    print(json.dumps({'dimension':args.dimension,'heads':args.heads,'directions':d.tolist(),
        'offset_interval':[1,1.125],'samples':args.samples,'status':'numerical_only'}),flush=True)
    for sample in range(args.samples):
        b=1+rng.uniform(.001,.124,args.heads)
        f=np.column_stack([np.ones(len(bits)),1/(bits@d.T+b)])
        patterns,condition,vertices=coverage(f,subsets,signs)
        seen[patterns]=True
        if sample<10 or sample%10==9 or np.all(seen):
            print(json.dumps({'sample':sample,'covered_complement_classes':int(np.sum(seen)),
                'total':len(seen),'condition':condition,'regular_vertices':vertices,
                'seconds':time.monotonic()-t}),flush=True)
        if np.all(seen): break
    missing=np.where(~seen)[0]
    report={'covered':int(np.sum(seen)),'total':len(seen),'missing':missing.tolist(),
        'directions':d.tolist(),'args':vars(args),'seconds':time.monotonic()-t}
    if args.output:
        with open(args.output,'w') as f: json.dump(report,f)
    print(json.dumps({'final_covered':report['covered'],'total':len(seen),
        'first_missing':missing[:32].tolist(),'seconds':report['seconds']}),flush=True)

if __name__=='__main__': main()
