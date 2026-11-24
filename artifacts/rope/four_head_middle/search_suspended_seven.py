"""Explore the selector suspension of the retained seven-bit example.

This eight-bit function is a new target, not the retained seven-bit separation.
Neither a failed fit nor an exact-score obstruction is a Boolean lower bound.
"""
import sys
import numpy as np
import search_fixed_denominator_lp as lp


def main():
    z=np.array([[2*((mask>>i)&1)-1 for i in range(8)] for mask in range(256)])
    y=np.sign(z[:,7]*sum(z[:,j+4]*(2*z[:,j]-z[:,3]) for j in range(3)))
    assert np.all(abs(y)==1)
    lp.N=8;lp.H=3;lp.NV=27;lp.ELL=27;lp.K=30;lp.BASE=33
    lp.Z=z;lp.Y=y;lp.X=np.c_[np.ones(len(z)),z]
    lp.main()


if __name__=='__main__':main()
