"""Run the LP/QP search on block-complemented local patterns.

Only whole-block complementation is used for the orientation obstruction.
These searches and any floating fits are not lower-bound certificates.
"""
import argparse
import importlib
import sys
import numpy as np
import search_fixed_denominator_lp as lp


def original_pattern():
    z=-np.ones(16);points=[z.copy()];labels=[-1]
    for i in range(16):
        row=z.copy();row[i]=1;points.append(row);labels.append(1)
    for i in range(8):
        for j in range(8):
            if i!=j:
                row=z.copy();row[i]=row[8+j]=1;points.append(row);labels.append(-1)
    for j in range(8):
        for k in range(j):
            row=z.copy();row[8+j]=row[8+k]=1;points.append(row);labels.append(-1)
    data={}
    for z,y in zip(points,labels):
        for flip in [-1,1]:
            for t in [-1,1]:data[tuple([t]+list(flip*z))]=t*y
    assert len(data)==404
    return np.array(list(data)),np.array(list(data.values()))


def main():
    ap=argparse.ArgumentParser(add_help=False)
    ap.add_argument('--engine',choices=['lp','qp'],default='lp')
    ap.add_argument('--original-pattern',action='store_true')
    ap.add_argument('--flip-y',action='store_true')
    a,rest=ap.parse_known_args()
    z,y=original_pattern() if a.original_pattern else lp.full_pattern()
    if a.flip_y:z[:,9:]*=-1
    x=np.c_[np.ones(len(z)),z]
    engine=lp if a.engine=='lp' else importlib.import_module('search_fixed_denominator_qp')
    for module in [lp,engine]:module.Z=z;module.Y=y;module.X=x
    sys.argv=[sys.argv[0]]+rest
    engine.main()


if __name__=='__main__':main()
