#!/usr/bin/env python3
"""Exact rational certificates, independent of the Lean proofs and search."""
from fractions import Fraction as Q
from itertools import product
import json

def determinant(a):
    a = [[Q(v) for v in row] for row in a]
    det = Q(1)
    for i in range(len(a)):
        j = next(j for j in range(i, len(a)) if a[j][i])
        if i != j:
            a[i], a[j] = a[j], a[i]
            det = -det
        pivot = a[i][i]
        det *= pivot
        for j in range(i+1, len(a)):
            r = a[j][i] / pivot
            for k in range(i, len(a)):
                a[j][k] -= r*a[i][k]
    return det

def one_head():
    xs = list(product((0, 1), repeat=6))
    basis = [7, 8, 13, 17, 19, 32, 43]
    values = [1, 1, 1, 1, -1, 1, -1]
    bs = [[1,1,2,1,1,1,1], [1,1,4,1,1,1,1]]
    aa = [[11,-9,-18,-9,-9,-9,11], [15,-13,-28,-13,-17,-13,19]]
    tables, records = [], []
    for a,b in zip(aa, bs):
        ds = [b[0]+sum(u*v for u,v in zip(b[1:], x)) for x in xs]
        scores = [Q(a[0]+sum(u*v for u,v in zip(a[1:],x)), den) for x,den in zip(xs,ds)]
        assert min(ds)>0 and all(abs(v)>=1 for v in scores)
        assert [scores[j] for j in basis] == values
        coeffs = [a[0]]+[a[j]-a[0]*b[j] for j in range(1,7)]
        assert max(map(abs,coeffs))<=88
        matrix = [[1]+[Q(t,ds[j]) for t in xs[j]] for j in basis]
        det = determinant(matrix)
        assert det != 0
        tables.append([v>0 for v in scores])
        records.append(dict(numerator=a,denominator=b,normalized_coefficients=coeffs,
                            basis_determinant=str(det),min_absolute_score=str(min(map(abs,scores)))))
    differing = [j for j in range(64) if tables[0][j]!=tables[1][j]]
    assert differing==[4]
    assert all((aa[0][i]>0)==(aa[1][i]>0) for i in range(1,7))
    constant=[3,-2,-4,-2,-2,-2,2]
    cscore=[constant[0]+sum(u*v for u,v in zip(constant[1:],x)) for x in xs]
    assert [cscore[j] for j in basis]==values
    assert cscore[4]==1
    return dict(dimension=6,width=1,basis_indices=basis,basis_values=values,
                examples=records,differing_indices=differing,
                constant_denominator_interpolant=constant)

def two_head():
    xs=list(product((0,1),repeat=3)); records=[]; tables=[]
    slopes=[[[1,1,2],[2,3,1]],[[1,1,1],[3,3,1]]]
    coeffs=[[3,4,Q(4,3),-12,-12,Q(-32,3),4],[-3,-6,-6,-24,28,28,32]]
    for b,c in zip(slopes,coeffs):
        features=[[Q(1)]+[Q(x[i],1+sum(u*v for u,v in zip(w,x))) for w in b for i in range(3)] for x in xs]
        scores=[sum(u*v for u,v in zip(c,row)) for row in features]
        assert min(map(abs,scores))>=1
        assert scores[1:]==[1,1,-1,1,-1,1,-1]
        assert max(map(abs,c))<=32
        det=determinant(features[1:]); assert det!=0
        records.append(dict(slopes=b,coefficients=list(map(str,c)),scores=list(map(str,scores)),basis_determinant=str(det)))
        tables.append([v>0 for v in scores])
    assert [j for j in range(8) if tables[0][j]!=tables[1][j]]==[0]
    return dict(dimension=3,width=2,examples=records)

if __name__=='__main__':
    print(json.dumps(dict(one_head=one_head(),two_head=two_head()),indent=2))
