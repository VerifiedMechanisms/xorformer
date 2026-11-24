"""Exact retained-RoPE upper bound for the seven-bit orientation example.

This does not prove the vanilla lower bound or a pure-RoPE upper bound of two.
It verifies two unrestricted positive affine ratios and constructs their retained
atoms using rational arithmetic. The existing vanilla lower bound is cited in
Theorem 15's corollary.
"""
import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path


def main():
    cert=json.loads(Path(__file__).with_name('retained_f7.json').read_text())
    Ds=cert['denominators'];Ns=cert['numerators'];atoms=[]
    for D,N in zip(Ds,Ns):
        assert len(D)==len(N)==8
        gap=D[0]-sum(abs(c) for c in D[1:]); assert gap>0
        C=[2*c for c in D[1:]]; A=[2*a for a in N[1:]]
        assert all(c!=0 for c in C)
        d=D[0]-sum(D[1:]);num=N[0]-sum(N[1:]);epsilon=F(gap,14)
        a=[max(-c,0)+epsilon for c in C];b=[aa+c for aa,c in zip(a,C)]
        gamma=d-sum(a);m=[F(aa,c) for aa,c in zip(A,C)];eta=num-sum(aa*mm for aa,mm in zip(a,m))
        assert gamma>0 and all(v>0 for v in a+b)
        atoms.append((a,b,gamma,m,eta))
    minimum=None
    for bits in product([0,1],repeat=7):
        z=[2*x-1 for x in bits];v=[1]+z
        target=sum(z[j+4]*(2*z[j]-z[3]) for j in range(3)); assert target!=0
        ds=[sum(a*b for a,b in zip(D,v)) for D in Ds]
        ns=[sum(a*b for a,b in zip(N,v)) for N in Ns]
        assert min(ds)>0
        cleared=ns[0]*ds[1]+ns[1]*ds[0];assert target*cleared>0
        minimum=abs(cleared) if minimum is None else min(minimum,abs(cleared))
        for h,(a,b,gamma,m,eta) in enumerate(atoms):
            weights=[b[i] if bits[i] else a[i] for i in range(7)]
            actual=(eta+sum(w*mm for w,mm in zip(weights,m)))/(gamma+sum(weights))
            assert actual==F(ns[h],ds[h])
    assert minimum==cert['minimum_integer_margin']
    print('VERIFIED: retained f7 uses two heads on all 128 inputs; rational atom construction checked.')

if __name__=='__main__':main()
