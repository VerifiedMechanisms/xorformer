#!/usr/bin/env python3
"""Build, then independently recheck, a rational common-normal certificate.

The default mode reads only the fixed rational certificate. Construction from
floating search data is optional and is never itself accepted as verification.
"""
from fractions import Fraction as F
from itertools import combinations
from math import lcm
from pathlib import Path
import argparse
import hashlib
import json

from verify_full_table_critical_points import inverse, mv, transpose, dot, determinant

BASE=Path(__file__).parent
CERT=BASE/'common-normal-maxima-certificate.json'


def rref(a):
    a=[[F(x) for x in row] for row in a]
    row=0;pivots=[]
    for col in range(len(a[0])):
        p=next((i for i in range(row,len(a)) if a[i][col]),None)
        if p is None: continue
        a[row],a[p]=a[p],a[row]
        scale=a[row][col]
        a[row]=[x/scale for x in a[row]]
        for i in range(len(a)):
            if i!=row:
                scale=a[i][col]
                a[i]=[x-scale*y for x,y in zip(a[i],a[row])]
        pivots.append(col);row+=1
        if row==len(a): break
    return a,pivots


def exact_data(n,a,b):
    codes=range(2**n)
    X=[[(x>>i)&1 for i in range(n)] for x in codes]
    Y=[[1]+x for x in X]
    D=[1+dot(b,x) for x in X]
    A=[dot(a,y) for y in Y]
    T=[aa/dd for aa,dd in zip(A,D)]
    J=[[F(v)/dd for v in y]+[-tt*F(v)/dd for v in x] for x,y,dd,tt in zip(X,Y,D,T)]
    keys=[min(x,(x&~3)|((x&1)<<1)|((x&2)>>1)) for x in codes]
    unique=sorted(set(keys))
    O=[[F(key==other) for other in unique] for key in keys]
    return X,D,A,T,J,O,unique


def ldl(a):
    n=len(a);L=[[F(i==j) for j in range(n)] for i in range(n)];p=[]
    for j in range(n):
        pivot=a[j][j]-sum(L[j][r]**2*p[r] for r in range(j))
        assert pivot>0,('nonpositive exact LDL pivot',j,pivot)
        p.append(pivot)
        for i in range(j+1,n):
            L[i][j]=(a[i][j]-sum(L[i][r]*L[j][r]*p[r] for r in range(j)))/pivot
    assert all(a[i][j]==sum(L[i][r]*p[r]*L[j][r] for r in range(n)) for i in range(n) for j in range(n))
    return L,p


def build(path, rounding_denominator=10000):
    candidates=[json.loads(s) for s in path.read_text().splitlines()]
    c=next(c for c in candidates if c['positive_mu_required'])
    n,a,b=c['n'],list(map(F,c['a'])),list(map(F,c['b']))
    X,D,A,T,J,O,keys=exact_data(n,a,b)
    eq=[[sum(J[x][i]*O[x][j] for x in range(len(X))) for j in range(len(keys))] for i in range(2*n+1)]
    rhs=[sum(J[x][i]*T[x] for x in range(len(X))) for i in range(2*n+1)]
    reduced,pivots=rref([row+[rhs[i]] for i,row in enumerate(eq)])
    assert len(pivots)==2*n+1 and max(pivots)<len(keys)
    z=[F(round(float(v)*rounding_denominator),rounding_denominator) for v in c['orbit_mu']]
    free=[j for j in range(len(keys)) if j not in pivots]
    for i,p in enumerate(pivots):
        z[p]=reduced[i][-1]-sum(reduced[i][j]*z[j] for j in free)
    assert all(dot(row,z)==r for row,r in zip(eq,rhs))
    assert min(z)>0
    Q=lcm(*(x.denominator for x in z))
    U=[int(x*Q) for x in z]
    report=dict(n=n,a=[int(x) for x in a],b=[int(x) for x in b],
        orbit_keys=keys,mu_denominator=Q,mu_numerators=U,
        scope='Exact four-bit full-affine common normal; two symmetry-related strict local maxima',
        source_trial=c['trial'],main_target_proved=False)
    CERT.write_text(json.dumps(report,indent=2)+'\n')


def verify():
    c=json.loads(CERT.read_text())
    n=c['n'];a=list(map(F,c['a']));b=list(map(F,c['b']))
    X,D,A,T,J,O,keys=exact_data(n,a,b)
    assert keys==c['orbit_keys'] and all(x>0 for x in b)
    Q=c['mu_denominator'];z=[F(x,Q) for x in c['mu_numerators']]
    assert min(z)>0
    mu=mv(O,z);R=[u-t for u,t in zip(mu,T)]
    p=2*n+1
    assert all(sum(R[x]*J[x][i] for x in range(len(X)))==0 for i in range(p))
    G=[[sum(row[i]*row[j] for row in J) for j in range(p)] for i in range(p)]
    _,gram_pivots=ldl(G)
    H=[[F(0) for _ in range(p)] for _ in range(p)]
    for x,dd,aa,tt,rr in zip(X,D,A,T,R):
        y=[1]+x
        for i in range(n+1):
            for j in range(n+1):
                H[i][j]+=F(y[i]*y[j])/dd**2
            for j in range(n):
                cross=(-tt+rr)*F(y[i]*x[j])/dd**2
                H[i][n+1+j]+=cross
                H[n+1+j][i]+=cross
        for i in range(n):
            for j in range(n):
                H[n+1+i][n+1+j]+=(tt*tt-2*rr*tt)*F(x[i]*x[j])/dd**2
    lower,hessian_pivots=ldl(H)
    L=lcm(*(int(x) for x in D))
    Ui=[int(u*Q) for u in mu]
    residual_numerators=[uu*int(dd)-Q*int(aa) for uu,dd,aa in zip(Ui,D,A)]
    for i in range(n+1):
        assert sum(r*([1]+x)[i]*int(dd)*(L//int(dd))**3 for r,x,dd in zip(residual_numerators,X,D))==0
    for i in range(n):
        assert sum(r*int(aa)*x[i]*(L//int(dd))**3 for r,x,dd,aa in zip(residual_numerators,X,D,A))==0
    M=[[int(Q*L**4*h) for h in row] for row in H]
    assert all(F(M[i][j],Q*L**4)==H[i][j] for i in range(p) for j in range(p))
    # Recover all denominator coefficients from singleton and pair entries.
    single=[T[1<<i] for i in range(n)]
    pairs=list(combinations(range(n),2))
    pair_matrix=[]
    for i,j in pairs:
        value=T[(1<<i)+(1<<j)]
        row=[F(0) for _ in range(n)]
        row[i]=value-single[i];row[j]=value-single[j]
        pair_matrix.append(row)
    _,selected=rref(transpose(pair_matrix))
    assert len(selected)==n
    reconstruction=[pair_matrix[j] for j in selected]
    assert determinant(reconstruction)!=0
    # The input swap preserves the functional, norm, and parameter domain.
    a2=a[:];b2=b[:];a2[1],a2[2]=a2[2],a2[1];b2[0],b2[1]=b2[1],b2[0]
    _,_,_,T2,J2,_,_=exact_data(n,a2,b2)
    assert T!=T2 and dot(T,T)==dot(T2,T2)
    assert all(sum((mu[x]-T2[x])*J2[x][i] for x in range(len(X)))==0 for i in range(p))
    assert dot(mu,T)==dot(T,T)==dot(mu,T2)
    report=dict(status='PASS',n=n,samples=len(X),parameter_dimension=p,
        all_functional_coefficients_positive=True,exact_stationarity_both_points=True,
        gram_positive_pivots=[str(x) for x in gram_pivots],
        least_squares_half_hessian_positive_pivots=[str(x) for x in hessian_pivots],
        half_hessian=[[str(x) for x in row] for row in H],
        lower_factor=[[str(x) for x in row] for row in lower],
        lower_inverse=[[str(x) for x in row] for row in inverse(lower)],
        reconstruction_pairs=[list(pairs[j]) for j in selected],
        reconstruction_determinant=str(determinant(reconstruction)),
        squared_table_norm=str(dot(T,T)),distinct_tables=True,
        common_denominator_lcm=L,cleared_hessian=M,
        certificate_sha256=hashlib.sha256(CERT.read_bytes()).hexdigest(),
        verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='Exact rational identities and strict positive definiteness; analytic implication is a written proof',
        main_target_proved=False)
    (BASE/'common-normal-maxima-rational-audit.json').write_text(json.dumps(report,indent=2)+'\n')
    hidden=['gram_positive_pivots','least_squares_half_hessian_positive_pivots','cleared_hessian','half_hessian','lower_factor','lower_inverse']
    print(json.dumps({k:v for k,v in report.items() if k not in hidden},indent=2))


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--build',type=Path)
    p.add_argument('--rounding-denominator',type=int,default=10000)
    args=p.parse_args()
    if args.build: build(args.build,args.rounding_denominator)
    verify()
