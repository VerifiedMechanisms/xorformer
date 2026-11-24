"""Actual pure-three search with separate auxiliary face backgrounds.

Each of the 36 cubic witnesses receives a different one-hot control context.
All core and auxiliary coordinates satisfy the same original pure-atom cone.
The 288 labels concern a partial cube; no success is accepted numerically.
"""
import itertools
from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'four_head_middle'))
import search_fixed_denominator_lp as lp


def pattern(binary=False):
    specifications=[]
    pairs=list(itertools.product(range(6,8),range(8,11)))
    for i in range(6):
        for col,(j,k) in enumerate(pairs):
            if i != col:specifications.append(([i],j,k,-1))
    for j,k in pairs:specifications.append((list(range(6)),j,k,1))
    aux=6 if binary else 36
    points=[];labels=[]
    for context,(xs,j,k,sign) in enumerate(specifications):
        for bits in itertools.product([-1,1],repeat=3):
            z=-np.ones(11+aux,dtype=int)
            if binary:z[11:]=2*((context>>np.arange(aux))&1)-1
            else:z[11+context]=1
            if sign==1:z[6:11]=1
            z[xs]=bits[0];z[j]=bits[1];z[k]=bits[2]
            points.append(z);labels.append(sign*np.prod(bits))
    return np.array(points),np.array(labels)


if __name__=='__main__':
    binary='--binary-contexts' in sys.argv
    if binary:sys.argv.remove('--binary-contexts')
    both='--hard-both' in sys.argv
    if both:sys.argv.remove('--hard-both')
    lp.Z,lp.Y=pattern(binary);lp.X=np.c_[np.ones(len(lp.Z)),lp.Z]
    lp.N,lp.H=lp.Z.shape[1],3;lp.NV=lp.H*(lp.N+1)
    lp.ELL,lp.K,lp.BASE=lp.NV,lp.NV+lp.H,lp.NV+2*lp.H
    if both:
        lp.HARD_MASK=np.zeros(len(lp.Y),dtype=bool)
        lp.HARD_MASK[:8]=True;lp.HARD_MASK[240:248]=True
    lp.main()
