#!/usr/bin/env python3
"""Exact Cauchy inverse, reflection, masks, and Schur identities."""
from fractions import Fraction as F
from flint import fmpq_mat
from math import prod
count=0
for H in range(1,10):
    p=[F(j*j+1,1000) for j in range(H)]
    C=fmpq_mat([[str(1/(1-a-b)) for b in p] for a in p])
    w=[prod((1-a-b for b in p),start=F(1))/prod((a-b for j,b in enumerate(p) if j!=i),start=F(1)) for i,a in enumerate(p)]
    W=fmpq_mat([[str(w[i] if i==j else 0) for j in range(H)] for i in range(H)])
    I=fmpq_mat([[int(i==j) for j in range(H)] for i in range(H)])
    B=C*W
    assert B*B==I and W*C*W==C.inv();count+=2
    for mask in range(min(1<<H,32)):
        D=fmpq_mat([[int(i==j)*(-1 if (mask>>i)&1 else 1) for j in range(H)] for i in range(H)])
        assert C*D*C.inv()==B*D*B;count+=1
    for removed in range(H):
        J=list(range(removed));K=list(range(removed,H))
        base=fmpq_mat([[C[i,j] for j in K] for i in K])
        if J:
            left=fmpq_mat([[C[i,j] for j in J] for i in K])
            middle=fmpq_mat([[C[i,j] for j in J] for i in J])
            base=base-left*middle.inv()*left.transpose()
        fac=[prod(((p[i]-p[j])/(1-p[i]-p[j]) for j in J),start=F(1)) for i in K]
        exact=fmpq_mat([[str(fac[i]*F(str(C[a,b]))*fac[j]) for j,b in enumerate(K)] for i,a in enumerate(K)])
        assert base==exact;count+=1
permutation=[0,3,1,2]
for r,t,sign in [([0,14,17,31],[229,245,338,379],-1),([0,8,13,21],[207,229,257,274],1)]:
    M=fmpq_mat([[str(1/(F(z-r[i])*F(z-r[permutation[i]]-100))) for z in t] for i in range(4)])
    assert sign*M.det()>0;count+=1
print('PASS:',count,'exact inverse, involution, masked conjugation, Schur, and paired-kernel checks')
