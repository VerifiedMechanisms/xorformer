"""Pure-four numerical search for the top-degree quartic orientation pattern.

This is the four-head counterpart of the cubic face pattern, with eight X
coordinates and three groups of two coordinates.  No numerical failure is a
lower bound and all prospective successes require exact certification.
"""
import itertools
from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'four_head_middle'))
import search_fixed_denominator_lp as lp


def pattern():
    points = {}
    def add(x, label):
        key = tuple(x)
        assert key not in points or points[key] == label
        points[key] = label
    triples = list(itertools.product(range(8,10),range(10,12),range(12,14)))
    for i in range(8):
        for col, triple in enumerate(triples):
            if i == col: continue
            for bits in itertools.product([-1,1],repeat=4):
                x = -np.ones(14,dtype=int)
                x[[i,*triple]] = bits
                add(x,-np.prod(bits))
    for triple in triples:
        for bits in itertools.product([-1,1],repeat=4):
            x = np.ones(14,dtype=int)
            x[:8] = bits[0]; x[list(triple)] = bits[1:]
            add(x,np.prod(bits))
    assert len(points) == 281
    return np.array(list(points)),np.array(list(points.values()))


if __name__ == '__main__':
    hard = '--hard-parity' in sys.argv
    if hard: sys.argv.remove('--hard-parity')
    anchors = '--hard-anchors' in sys.argv
    if anchors: sys.argv.remove('--hard-anchors')
    lp.Z,lp.Y = pattern();lp.X = np.c_[np.ones(len(lp.Z)),lp.Z]
    lp.N,lp.H = 14,4;lp.NV=lp.H*(lp.N+1)
    lp.ELL,lp.K,lp.BASE=lp.NV,lp.NV+lp.H,lp.NV+2*lp.H
    if hard or anchors:
        other=[i for i in range(14) if i not in [0,8,10,13]]
        lp.HARD_MASK=np.all(lp.Z[:,other]==-1,axis=1)
        if anchors:lp.HARD_MASK |= np.all(lp.Z==1,axis=1)
    lp.main()
