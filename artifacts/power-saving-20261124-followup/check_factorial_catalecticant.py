#!/usr/bin/env python3
"""Exact rational rank check for the curved reciprocal-jet catalecticant."""
from fractions import Fraction
from math import factorial, comb
import json

def rank(A):
    A=[list(map(Fraction,row)) for row in A]
    r=0
    for c in range(len(A[0])):
        p=next((i for i in range(r,len(A)) if A[i][c]),None)
        if p is None: continue
        A[r],A[p]=A[p],A[r]
        z=A[r][c]
        A[r]=[v/z for v in A[r]]
        for i in range(r+1,len(A)):
            z=A[i][c]
            if z: A[i]=[v-z*w for v,w in zip(A[i],A[r])]
        r+=1
    return r

out=[]
for m in range(1,13):
    idx=[(a,b,m-a-b) for a in range(m+1) for b in range(m-a+1)]
    A=[]
    for a,b,c in idx:
        row=[]
        for d,e,f in idx:
            j=a+d
            row.append((-1)**j*factorial(j)*factorial(2*m-j) if j==b+e else 0)
        A.append(row)
    out.append(dict(m=m,local_length=2*m+1,middle_dimension=comb(m+2,2),exact_rank=rank(A)))
print(json.dumps(out,indent=2))
