#!/usr/bin/env python3
"""Exact integer moment relations and finite-field certificates of rational rank.
A nonzero minor modulo the displayed prime certifies a nonzero integer minor.
No numerical tolerance or probabilistic inference is used.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial, prod
from pathlib import Path
import hashlib,json

BASE=Path(__file__).resolve().parent
PRIME=1000000007


def independent_rows(rows, width):
    basis={};selected=[];pivots=[]
    for label,row in rows:
        a=[v%PRIME for v in row[:width]]
        for j,b in sorted(basis.items()):
            if a[j]:
                c=a[j];a=[(x-c*y)%PRIME for x,y in zip(a,b)]
        if not any(a):continue
        j=next(i for i,v in enumerate(a) if v)
        pivot=a[j];inverse=pow(pivot,-1,PRIME)
        basis[j]=[(v*inverse)%PRIME for v in a]
        selected.append(label);pivots.append(pivot)
        if len(basis)==width:break
    assert len(basis)==width,(width,len(basis))
    return {'prime':PRIME,'columns':list(range(width)),'rows':selected,'nonzero_pivots':pivots}


def construct(n,m):
    L=2;dim=2
    line=[((L+4*h,)*dim,(-1)**(m-h)*comb(m,h)) for h in range(1,m+1)]
    cluster=[((L,)*dim,(-1)**m)]
    records=[]
    for r in range(n-2):
        p,c=cluster[0];roots={L}|{v[1] for v,_ in cluster}
        T=1+max(abs(q-p[1]) for q in roots);shift=T+1
        L+=shift
        def extend(items):
            out=[]
            for v,c in items:
                w=tuple(a+shift for a in v)
                out.append((w+(w[0],),c))
            return out
        line=extend(line);cluster=extend(cluster);dim+=1
        p,c=cluster[0];roots={L}|{v[1] for v,_ in cluster}
        new=[]
        for alpha,beta,sign in ((1,1,-1),(0,2,1),(1,0,1),(-1,2,-1),(-1,1,1)):
            w=list(p);w[1]+=T*alpha;w[-1]+=T*beta
            new.append((tuple(w),c*sign))
        assert len(roots)<=2*r+1<=m-1
        def q(z):return prod(z-a for a in roots)
        assert all(q(v[1])-q(v[0])==0 for v,_ in line+cluster)
        sep=q(new[2][0][1])-q(new[2][0][0]);assert sep!=0
        assert all(v[-1]==v[0] for v,_ in line+cluster)
        # Exact affine replacement and coefficient sum.
        signs=(-1,1,1,-1,1)
        assert sum(signs)==1
        assert all(sum(s*v[j] for s,(v,_) in zip(signs,new))==p[j] for j in range(dim))
        cluster=cluster[1:]+new
        points=line+cluster
        assert len(set(v for v,_ in points))==len(points)
        assert all(min(v)>0 and c!=0 for v,c in points)
        assert all(v[0]==L for v,_ in cluster)
        assert sum(c for _,c in cluster)==(-1)**m
        records.append({'step':r+1,'dimension':dim,'T':T,'translation':shift,
                        'separator_roots':sorted(roots),'separator_value':sep})
    return L,line+cluster,records


def check_case(n,m):
    L,points,steps=construct(n,m)
    H=len(points);assert H==m+4*n-7
    velocities=[v for v,c in points];weights=[c for v,c in points]
    samples=list(product((0,1),repeat=n));moment_checks=0
    def rows():
        nonlocal moment_checks
        for mask,x in enumerate(samples):
            projections=[sum(a*b for a,b in zip(v,x)) for v in velocities]
            row=[1]*H
            for degree in range(m):
                assert sum(a*b for a,b in zip(weights,row))==0
                moment_checks+=1
                yield [mask,degree],row
                row=[a*b for a,b in zip(row,projections)]
    # Use selected rows to certify rank H-1; independently replay every row.
    minor=independent_rows(rows(),H-1)
    moment_checks=0
    for _ in rows():pass
    affine_minor=independent_rows(((i,[1]+list(v)) for i,v in enumerate(velocities)),n+1)
    first=sum(c*v[0]**m for v,c in points);assert first==4**m*factorial(m)
    rational_checks=0
    for x in samples:
        t=sum(x);D=1+t
        projections=[sum(a*b for a,b in zip(v,x)) for v in velocities]
        for eps in (F(1,7),F(1)):
            score=sum((F(c,D+eps*p) for c,p in zip(weights,projections)),F(0))
            direct=sum((F((-1)**(m-h)*comb(m,h),D+eps*(L+4*h)*t) for h in range(m+1)),F(0))
            closed=F((-1)**m*factorial(m))*(4*eps*t)**m/prod(D+eps*(L+4*h)*t for h in range(m+1))
            assert score==direct==closed
            assert 1+(-1)**m*score>0
            rational_checks+=1
    return {'n':n,'m':m,'H':H,'L':L,'velocities':velocities,'residues':weights,
            'steps':steps,'moment_rank':H-1,'moment_rank_certificate':minor,
            'affine_rank':n+1,'affine_rank_certificate':affine_minor,
            'first_nonzero_anchor_moment':first,'integer_moment_checks':moment_checks,
            'rational_score_checks':rational_checks}


if __name__=='__main__':
    cases=[]
    for n,m in [(n,2*n) for n in range(3,11)]+[(n,n*n) for n in range(3,8)]:
        c=check_case(n,m);cases.append(c)
        print(n,m,c['H'],c['moment_rank'],'PASS',flush=True)
    result={'status':'PASS','cases':cases,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'arithmetic':'Exact integers and Fractions. Nonzero minors modulo 1000000007 certify exact rational rank lower bounds; explicit full-support integer relations certify matching upper bounds.',
            'scope':'Finite construction replay. General induction has a written proof. No asymptotic head lower bound.',
            'main_target_proved':False}
    (BASE/'moment-circuit-surgery-rational-audit.json').write_text(json.dumps(result,indent=2)+'\n')
