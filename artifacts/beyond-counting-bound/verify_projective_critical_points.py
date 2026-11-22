"""Exact ingredient checks for the projectively normalized critical-point proof.

The implicit-function argument is written, not replaced by these finite checks.
In particular this program does not enumerate perturbed roots or prove a head
lower bound. Every operation affecting a reported identity is rational.
"""
from fractions import Fraction as F
import itertools
import json
from pathlib import Path

import sympy as sp


def check(d,k):
    N=2**d;q=N//2-1
    a=[2**i for i in range(d)];A=[1+x for x in a]
    t=sp.Symbol('t')
    Q=sp.prod(t-i for i in range(1,q+1))
    Dstar=sp.prod(t+i for i in range(2,N+1))
    D=(1+t)*Dstar;P=Dstar-Q**2
    derivative=sp.diff(D,t)
    coefficients=[F(P.subs(t,-c)/derivative.subs(t,-c)) for c in range(1,N+1)]
    assert sp.cancel(sum(sp.Rational(v.numerator,v.denominator)/(t+c)
                         for c,v in enumerate(coefficients,1))-P/D)==0
    H=sp.Matrix([[-int(i==j)+sp.Rational(A[i],N) for j in range(d)] for i in range(d)])
    Hinv=sp.Matrix([[-int(i==j)+sp.Rational(A[i],d-1) for j in range(d)] for i in range(d)])
    assert H*Hinv==sp.eye(d)
    assert H.det()==(-1)**(d+1)*sp.Rational(d-1,N)
    data={}
    for ell in range(1,q+1):
        R=sum(v/F(c+ell) for c,v in enumerate(coefficients,1))
        Rt=-sum(v/F(c+ell)**2 for c,v in enumerate(coefficients,1))
        Rtt=2*sum(v/F(c+ell)**3 for c,v in enumerate(coefficients,1))
        v=(1+ell)*R;vt=R+(1+ell)*Rt;vtt=2*Rt+(1+ell)*Rtt
        expected=-2*F(sp.diff(Q,t).subs(t,ell))**2/F(Dstar.subs(t,ell))
        assert v==1 and vt==0 and vtt==expected and vtt<0
        va=[-(1+ell)*sum(coefficients[c-1]*((c-1>>i)&1)/F(c+ell)**2
                           for c in range(1,N+1)) for i in range(d)]
        vat=[sum(coefficients[c-1]*((c-1>>i)&1)*
                  (-1/F(c+ell)**2+2*(1+ell)/F(c+ell)**3)
                  for c in range(1,N+1)) for i in range(d)]
        vaa=[[2*(1+ell)*sum(coefficients[c-1]*((c-1>>i)&1)*((c-1>>j)&1)
                  /F(c+ell)**3 for c in range(1,N+1)) for j in range(d)] for i in range(d)]
        data[ell]=(vtt,sp.Matrix(va),sp.Matrix(vat),sp.Matrix(vaa))
    # Full rational Jacobian checks for the smaller cases. Larger dimensions
    # retain all scalar checks and the explicit block determinant formula.
    grids=list(itertools.product(range(1,q+1),repeat=k)) if d<=4 else [(1,)*k,(q,)*k]
    determinants=[]
    for ell in grids:
        z=-Hinv.T*sum((data[e][1] for e in ell),sp.zeros(d,1))
        assert H.T*z+sum((data[e][1] for e in ell),sp.zeros(d,1))==sp.zeros(d,1)
        pair=sp.zeros(d+k)
        row=0
        for j,e in enumerate(ell):
            pair[row,0]=1+e;pair[row,d+j]=-a[0];row+=1
        for i in range(1,d):
            pair[row,i]=1+ell[0];pair[row,d]=-a[i];row+=1
        pair[row,d]=1;pair[row,d+1]=1
        assert pair.det()!=0
        det_expected=H.det()**2*sp.prod(data[e][0] for e in ell)
        assert det_expected!=0
        if d<=3:
            J=sp.zeros(2*d+k)
            J[:d,:d]=H
            for j,e in enumerate(ell):
                J[d+j,:d]=data[e][2].T
                J[d+j,d+j]=data[e][0]
            B=sp.zeros(d)
            for i in range(d):
                for l in range(d):
                    for r in range(d):
                        Gil=-sp.Rational(int(r==l),A[r])+sp.Rational(1,N)
                        Gij=-sp.Rational(int(r==i),A[r])+sp.Rational(1,N)
                        Gijl=2*sp.Rational(int(r==i==l),A[r]**2)-sp.Rational(2,N**2)
                        B[i,l]+=(int(r==i)*Gil+int(r==l)*Gij+A[r]*Gijl)*z[r]
                    for e in ell:
                        B[i,l]+=data[e][3][i,l]+data[e][1][i]*data[e][1][l]
            J[d+k:,:d]=B
            for j,e in enumerate(ell):J[d+k:,d+j]=data[e][2]
            J[d+k:,d+k:]=H.T
            assert J.det()==det_expected
        determinants.append(str(det_expected))
    return {'d':d,'k':k,'n':d+k,'scalar_locations':q,
            'theorem_branch_count':q**k,'grid_ingredient_checks':len(grids),
            'full_jacobian_checks':len(grids) if d<=3 else 0,
            'transverse_determinant':str(H.det()),
            'first_grid_jacobian_determinant':determinants[0],
            'exact_partial_fractions':True,'exact_scalar_critical_identities':True,
            'exact_pair_reconstruction':True,'perturbed_roots_enumerated':False,
            'target_lower_bound_proved':False}


if __name__=='__main__':
    results=[check(d,k) for d,k in [(2,2),(3,2),(3,3),(4,2),(5,2)]]
    path=Path(__file__).with_name('projective-critical-point-checks.json')
    path.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
