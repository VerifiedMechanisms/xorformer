#!/usr/bin/env python3
"""Exact finite replay; the arbitrary-dimension claims have written proofs."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import random
import sympy as sp

BASE = Path(__file__).resolve().parent


def monomials(n, degree):
    if n == 1:
        yield (degree,)
    else:
        for j in range(degree + 1):
            for tail in monomials(n - 1, degree - j):
                yield (j,) + tail


def plus(alpha, i, amount=1):
    a = list(alpha)
    a[i] += amount
    assert min(a) >= 0
    return tuple(a)


def vector(*terms):
    result = defaultdict(int)
    for coefficient, alpha, tag in terms:
        result[(alpha, tag)] += coefficient
    return {key: value for key, value in result.items() if value}


def shift(a, alpha, scale=1):
    return { (tuple(i+j for i,j in zip(m,alpha)),tag):scale*c
             for (m,tag),c in a.items() }


def add(*vectors):
    out = defaultdict(int)
    for a in vectors:
        for key,c in a.items():
            out[key] += c
    return {key:c for key,c in out.items() if c}


def generators(n):
    z=(0,)*n
    a = [vector((1,plus(z,i),-1),(-1,plus(z,i),i)) for i in range(n)]
    b = {(i,j):vector((1,plus(z,i),j),(-1,plus(z,j),i))
         for i in range(n) for j in range(n) if i!=j}
    return a,b


def reduce_tagged(alpha, tag):
    n=len(alpha);degree=sum(alpha);a,b=generators(n);steps=0
    if tag == -1:
        i=next(i for i,v in enumerate(alpha) if v)
        old=vector((1,alpha,tag),(-1,alpha,i))
        assert old == shift(a[i],plus(alpha,i,-1))
        tag=i;steps+=1
    support={i for i,v in enumerate(alpha) if v}|{tag}
    r=max(support)
    if tag!=r:
        new=plus(plus(alpha,r,-1),tag)
        assert vector((1,alpha,tag),(-1,new,r)) == shift(b[r,tag],plus(alpha,r,-1))
        alpha=new;tag=r;steps+=1
    for i in sorted(support-{r}):
        while alpha[i]>=2:
            new=plus(plus(alpha,i,-1),r)
            multiplier=plus(alpha,i,-2)
            rhs=add(shift(b[i,r],plus(multiplier,i)),
                    shift(a[i],plus(multiplier,r),-1),
                    shift(a[r],plus(multiplier,i)))
            assert vector((1,alpha,r),(-1,new,r)) == rhs
            alpha=new;steps+=3
    target=tuple((degree-len(support)+1 if i==r else 1 if i in support else 0) for i in range(n))
    assert alpha==target and tag==r and steps<=3*degree+2
    return alpha,tag,support,steps


def normal_form_audit():
    counts={'tagged_monomials':0,'generator_multiples':0,'quotient_dimensions':0,'boolean_evaluations':0}
    for n in range(1,7):
        for k in range(1,7):
            normal=set()
            for alpha in monomials(n,k):
                for tag in range(-1,n):
                    beta,r,support,steps=reduce_tagged(alpha,tag)
                    normal.add((beta,r));counts['tagged_monomials']+=1
                    counts['generator_multiples']+=steps
                    for x in product((0,1),repeat=n):
                        lhs=(1 if tag==-1 else x[tag])
                        rhs=x[r]
                        for v,e,f in zip(x,alpha,beta):
                            lhs*=v**e;rhs*=v**f
                        assert lhs==rhs==int(all(x[i] for i in support))
                        counts['boolean_evaluations']+=1
            expected=sum(comb(n,s) for s in range(1,min(k+1,n)+1))
            assert len(normal)==expected
            sets=sorted((frozenset(i for i,v in enumerate(a) if v)|{tag} for a,tag in normal),key=lambda s:(len(s),sorted(s)))
            assert len(set(sets))==expected
            # The inclusion matrix is triangular with unit diagonal.
            for i,s in enumerate(sets):
                for j,t in enumerate(sets):
                    if j>i: assert not t<=s
            counts['quotient_dimensions']+=1
    return counts


def components(n,edges):
    parent=list(range(n))
    def root(i):
        while parent[i]!=i:i=parent[i]
        return i
    for i,j in edges:parent[root(i)]=root(j)
    return len({root(i) for i in range(n)})


def graph_check(n,edges):
    velocities=[]
    for i,j in edges:
        a=[0]*n;b=[0]*n;a[i]=2;a[j]=1;b[i]=1;b[j]=2
        velocities.extend((tuple(a),tuple(b)))
    rows=[]
    for x in product((0,1),repeat=n):
        projections=[sum(a*b for a,b in zip(v,x)) for v in velocities]
        rows += [[int(p==m) for p in projections] for m in range(4)]
    if not edges:return 0
    rank=sp.Matrix(rows).rank()
    expected=len(edges)+n-components(n,edges)
    assert rank==expected
    # Independent direct constraints: paired residues cancel, then divergence.
    constraints=[]
    for e in range(len(edges)):
        row=[0]*len(velocities);row[2*e]=row[2*e+1]=1;constraints.append(row)
    for i in range(n):
        row=[0]*len(velocities)
        for e,(a,b) in enumerate(edges):
            if i==a:row[2*e]=1
            if i==b:row[2*e+1]=1
        constraints.append(row)
    assert sp.Matrix(constraints).rank()==rank
    assert sp.Matrix(rows+constraints).rank()==rank
    return rank


def coefficient_rows(velocities,degree):
    # Homogeneous affine forms with constant variable z_0.
    rows=[]
    for alpha in monomials(len(velocities[0])+1,degree):
        mult=factorial(degree)
        for v in alpha:mult//=factorial(v)
        row=[]
        for velocity in velocities:
            c=mult
            for v,e in zip((1,)+velocity,alpha):c*=v**e
            row.append(c)
        rows.append(row)
    return rows


def graph_audit():
    total=0;rng=random.Random(233181)
    for n in range(2,5):
        pairs=list(combinations(range(n),2))
        for mask in range(1<<len(pairs)):
            edges=[p for i,p in enumerate(pairs) if mask>>i&1]
            graph_check(n,edges);total+=1
    for n in (5,6):
        pairs=list(combinations(range(n),2))
        for _ in range(5):
            edges=[p for p in pairs if rng.randrange(2)]
            graph_check(n,edges);total+=1
    cycles=[];rational_checks=0
    for n in range(3,9):
        edges=[(i,(i+1)%n) for i in range(n)]
        velocities=[]
        for i,j in edges:
            a=[0]*n;b=[0]*n;a[i]=2;a[j]=1;b[i]=1;b[j]=2
            velocities.extend((tuple(a),tuple(b)))
        square=sp.Matrix(coefficient_rows(velocities,2))
        cube=sp.Matrix(coefficient_rows(velocities,3))
        c=sp.Matrix([1,-1]*n)
        assert square*c==sp.zeros(square.rows,1)
        assert square.rank()==2*n-1 and cube.rank()==2*n
        assert sp.Matrix([[1]+list(v) for v in velocities]).rank()==n
        for x in product((0,1),repeat=n):
            p=[sum(a*b for a,b in zip(v,x)) for v in velocities]
            for m in range(9):
                assert sum((-1)**i*(1+v)**m for i,v in enumerate(p))==0
            for eps in (F(0),F(1,3),F(2)):
                D=1+sum((i+1)*v for i,v in enumerate(x))
                assert sum((F((-1)**i,D+eps*v) for i,v in enumerate(p)),F(0))==0
                rational_checks+=1
        cycles.append({'n':n,'heads':2*n,'square_rank':2*n-1,'cube_rank':2*n,'affine_dimension':n-1})
    return {'graphs':total,'cycles':cycles,'reciprocal_checks':rational_checks}


def contact_circuit_audit():
    cases=[]
    switch=[(3,3,2),(2,4,2),(3,2,2),(1,4,2),(1,3,2)]
    replacement=[-1,1,1,-1,1]
    for m in range(3,13):
        line=[(2+4*h,)*3 for h in range(1,m+1)]
        velocities=line+switch
        weights=[(-1)**(m-h)*comb(m,h) for h in range(1,m+1)]+[(-1)**m*r for r in replacement]
        rows=[]
        for x in product((0,1),repeat=3):
            p=[sum(a*b for a,b in zip(v,x)) for v in velocities]
            for j in range(m):
                row=[v**j for v in p]
                assert sum(a*b for a,b in zip(row,weights))==0
                rows.append(row)
            for eps in (F(1,7),F(1),F(3)):
                D=1+sum(x)
                score=sum((F(c,D+eps*v) for c,v in zip(weights,p)),F(0))
                original=sum((F((-1)**(m-h)*comb(m,h),D+eps*(2+4*h)*sum(x)) for h in range(m+1)),F(0))
                assert score==original
        rank=sp.Matrix(rows).rank()
        assert rank==m+4
        assert sp.Matrix([[1]+list(v) for v in velocities]).rank()==4
        first=sum(c*v[2]**m for c,v in zip(weights,velocities))
        assert first==4**m*factorial(m)
        cases.append({'m':m,'heads':m+5,'moment_rank':rank,'affine_dimension':3,'first_nonzero_moment':first})
    return cases


if __name__=='__main__':
    result={'status':'PASS','normal_forms':normal_form_audit(),'graphs':graph_audit(),'contact_circuits':contact_circuit_audit(),
            'arithmetic':'Integer polynomial coefficients, rational reciprocals, exact SymPy ranks',
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope':'Finite exact replay, not proof of arbitrary-dimension assertions or main target',
            'main_target_proved':False}
    (BASE/'affine-projection-rational-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
