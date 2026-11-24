#!/usr/bin/env python3
"""Exploratory filtered reciprocal-kernel ratios; not a proof.

One full Boolean finite difference with positive slopes w is
K_w(d) = sum_{T subset [c]} (-1)^(c-|T|)/(d-sum_{i in T}w_i), d>sum w.
This script counts robust sampled turns of ratios for randomly chosen positive
slopes normalized to total 1. Any candidate is rechecked with mpmath.
"""
import argparse, json, math
import numpy as np
import mpmath as mp


def subsets(weights):
    vals = np.array([0], dtype=np.longdouble)
    signs = np.array([1], dtype=np.longdouble)
    for w in weights:
        vals = np.r_[vals, vals + w]
        signs = np.r_[-signs, signs]
    return vals, signs


def kernel(weights, grid):
    poles, signs = subsets(weights)
    return np.sum(signs[:,None]/(grid[None,:]-poles[:,None]), axis=0)


def mp_kernel(weights, d):
    poles, signs = [mp.mpf(0)], [1]
    for w in weights:
        poles = poles + [x+w for x in poles]
        signs = [-x for x in signs] + signs
    return mp.fsum(s/(d-p) for s,p in zip(signs,poles))


def turns(vec, tolerance):
    differences = np.diff(vec)
    signs = np.sign(differences[np.abs(differences)>tolerance])
    return int(np.sum(signs[1:] != signs[:-1]))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--c', type=int, default=6)
    ap.add_argument('--pairs', type=int, default=300)
    ap.add_argument('--seed', type=int, default=1729)
    args=ap.parse_args()
    rng=np.random.default_rng(args.seed)
    grid=(1+np.geomspace(1e-5,3,220)).astype(np.longdouble)
    best=-1
    for it in range(args.pairs):
        w=rng.uniform(.2,2,args.c).astype(np.longdouble); w/=sum(w)
        v=rng.uniform(.2,2,args.c).astype(np.longdouble); v/=sum(v)
        ratios=kernel(w,grid)/kernel(v,grid)
        ct=turns(ratios, np.longdouble('1e-8'))
        if ct>best:
            mp.mp.dps=70
            wm=[mp.mpf(str(x)) for x in w]; wm=[x/sum(wm) for x in wm]
            vm=[mp.mpf(str(x)) for x in v]; vm=[x/sum(vm) for x in vm]
            precise=[mp_kernel(wm,mp.mpf(str(d)))/mp_kernel(vm,mp.mpf(str(d))) for d in grid]
            dif=[precise[i+1]-precise[i] for i in range(len(precise)-1)]
            sg=[mp.sign(x) for x in dif if abs(x)>mp.mpf('1e-30')]
            verified=sum(sg[i+1]!=sg[i] for i in range(len(sg)-1))
            if verified>best:
                best=verified
                print(json.dumps({'iteration':it,'c':args.c,'sampled_turns':best,
                    'w':[str(x) for x in wm],'v':[str(x) for x in vm]}),flush=True)
    print(json.dumps({'status':'finite sample only','c':args.c,'pairs':args.pairs,
        'seed':args.seed,'maximum_sampled_turns':best}),flush=True)

if __name__=='__main__': main()
