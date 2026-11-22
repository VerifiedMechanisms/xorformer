#!/usr/bin/env python3
"""Independent exact finite audits of the written geometric-product theorem.

All transcendental estimates are enclosed by rational atanh-series bounds.
No floating-point conclusion, theorem prover assumption, or asymptotic head
bound is inferred from these checks.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import comb
from pathlib import Path
import json
import numpy as np

@lru_cache(None)
def log_bounds(q, terms=128):
    q = F(q)
    assert q >= 1
    k = 0
    while q >= 2:
        q /= 2
        k += 1
    def small(x):
        t = (x-1)/(x+1)
        lo = sum((2*t**(2*j+1)/F(2*j+1) for j in range(terms)), F(0))
        rem = 2*t**(2*terms+1)/(F(2*terms+1)*(1-t*t))
        return lo, lo+rem
    lo, hi = small(q)
    if k:
        l2, h2 = small(F(2))
        lo, hi = lo+k*l2, hi+k*h2
    return lo, hi

def coefficient_bounds(n,t):
    lo=hi=F(0)
    for u in range(t+1):
        a,b=log_bounds(F(1+n-u))
        sign=-((-1)**(t-u))*comb(t,u)
        if sign>=0:lo+=sign*a;hi+=sign*b
        else:lo+=sign*b;hi+=sign*a
    return lo,hi

def main():
    rows=[]
    inverse_entries=0
    for n in range(1,9):
        N=2**n;full=N-1; masks=list(range(1,N))
        C=np.array([[int(s&t!=0) for t in masks] for s in masks],dtype=np.int64)
        R=np.array([[(-1)**((s&t).bit_count()+1) if s|t==full else 0
                     for t in masks] for s in masks],dtype=np.int64)
        assert np.array_equal(C@R,np.eye(N-1,dtype=np.int64))
        assert max(abs(R).sum(axis=1))<=N
        inverse_entries+=(N-1)**2
        mu=F(1,8*N*N);a=128*n*(n+1)*N**4;delta=F(1,128*n*N**3)
        rho=F(N*N*(n+1),a);eps=F(1,128*N**3)
        assert rho<F(1,2)
        assert N*n*delta==mu/16 and rho*n==mu/16 and 4*N*eps==mu/4
        assert F(N,a)*(n+mu/2)<F(1,2)
        # For a>=256, exp(-a)<2^-256, since log(2)<1.
        assert a>=256
        max_entry=F(0)
        for size in range(1,n+1):
            v0lo,v0hi=log_bounds(1+delta*size)
            for k in range(1,size+1):
                l=size-k
                llo,lhi=log_bounds(F(k))
                # log(k+exp(-a)*(1+delta*l))-log(k) is in [0,2^-255].
                elo=(llo-v0hi)/a
                ehi=(lhi+F(1,2**255)-v0lo)/a
                bound=max(abs(elo),abs(ehi))
                assert bound <= F(n+1,a)
                max_entry=max(max_entry,bound)
        rows.append({'n':n,'N':N,'inverse_entries_checked':(N-1)**2,
                     'inverse_max_row_sum':int(max(abs(R).sum(axis=1))),
                     'rho_bound':str(rho),'epsilon_radius':str(eps),
                     'all_budget_checks':'PASS','entry_bound_checks':'PASS'})
    coefficients=[]
    for n in range(1,21):
        mu=F(1,8*4**n)
        intervals=[coefficient_bounds(n,t) for t in range(1,n+1)]
        assert all(lo>=mu for lo,hi in intervals)
        lo=sum((comb(n,t)*intervals[t-1][0] for t in range(1,n+1)),F(0))
        hi=sum((comb(n,t)*intervals[t-1][1] for t in range(1,n+1)),F(0))
        g0,g1=log_bounds(F(n+1))
        assert lo<=g1 and g0<=hi
        coefficients.append({'n':n,'coefficients_checked':n,'minimum_lower_bound':str(mu),
                             'positive_integral_lower_bound':'PASS','coverage_total':'PASS'})
    out={'status':'PASS','arithmetic':'integer matrices and rational logarithm enclosures',
         'inverse_entries_checked':inverse_entries,'matrix_checks':rows,
         'coefficient_checks':coefficients,'head_complexity_conclusion':None,
         'scope':'finite ingredient checks; general theorem is the written proof'}
    path=Path(__file__).with_name('geometric-tangent-checks.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','inverse_entries_checked':inverse_entries,
                      'positive_coefficients_checked':sum(range(1,21))}))

if __name__=='__main__':main()
