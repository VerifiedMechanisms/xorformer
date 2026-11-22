#!/usr/bin/env python3
"""Independent exact verifier using scalar derivative bounds, no interval class."""
from fractions import Fraction as F
import json
from pathlib import Path
import sys


def check(path):
    data=json.loads(Path(path).read_text());src=data['source']
    n,h=src['n'],src['heads'];d=2*n*h
    assert n==5 and h==2 and d==20
    assert len(src['indices'])==d and len(set(src['indices']))==d
    assert all(0<i<2**n for i in src['indices'])
    c=[F(v) for v in data['center']];r=F(data['radius'])
    source=[F(v,src['scale']) for field in ['u_numerator','b_numerator'] for row in src[field] for v in row]
    R=[[F(v) for v in row] for row in data['inverse']]
    R0=[[F(v) for v in row] for row in data['source_inverse']]
    assert len(c)==len(source)==d and r>0
    assert len(R)==len(R0)==d and all(len(row)==d for row in R+R0)
    assert all(v-r>F(1,3) for v in c[n*h:])
    assert all(v>0 for v in source[n*h:])
    def xrow(v):return [(v>>i)&1 for i in range(n)]
    def parts(p,x):
        return [(sum(p[k*n+i]*x[i] for i in range(n)),1+sum(p[h*n+k*n+i]*x[i] for i in range(n))) for k in range(h)]
    def value(p,x):return sum(a/b for a,b in parts(p,x))
    def derivative(p,x):
        pairs=parts(p,x)
        return [F(x[i],1)/b for a,b in pairs for i in range(n)]+[-a*x[i]/b**2 for a,b in pairs for i in range(n)]
    def mat_error(R,J):
        return max(sum(abs(F(i==j)-sum(R[i][k]*J[k][j] for k in range(d))) for j in range(d)) for i in range(d))
    inputs=[xrow(v) for v in src['indices']]
    J=[derivative(c,x) for x in inputs]
    J0=[derivative(source,x) for x in inputs]
    residual=[value(c,x)-value(source,x) for x in inputs]
    E=max(abs(sum(R[i][j]*residual[j] for j in range(d))) for i in range(d))
    Rnorm=max(sum(abs(v) for v in row) for row in R)
    # If k coordinates of x are one, A and B change by at most k*r.
    # Bound the change of every partial derivative throughout the box.
    jac_changes=[]
    for x in inputs:
        k=sum(x);delta=k*r;entry_sum=F(0)
        for a,b in parts(c,x):
            lower=b-delta
            assert lower>0
            du=delta/(lower*b)
            db=delta/lower**2+abs(a)*delta*(2*b+delta)/(lower**2*b**2)
            entry_sum+=k*(du+db)
        jac_changes.append(entry_sum)
    q=mat_error(R,J)+Rnorm*max(jac_changes)
    source_error=mat_error(R0,J0)
    assert E<F('1e-70') and q<F('1e-20') and source_error<F('1e-70')
    assert E+q*r<r
    heldout=[]
    for v in range(1,2**n):
        if v in src['indices']:continue
        x=xrow(v);delta=sum(x)*r;err=F(0)
        for a,b in parts(c,x):
            lower=b-delta
            assert lower>0
            err+=delta/lower+abs(a)*delta/(lower*b)
        difference=value(c,x)-value(source,x)
        if difference-err>F(1,10) or difference+err<-F(1,10):heldout.append(v)
    assert heldout==[4,8]
    result={'status':'VERIFIED','method':'independent scalar derivative bounds',
            'E_less_than':'1e-70','q_less_than':'1e-20','source_inverse_error_less_than':'1e-70',
            'radius':str(r),'candidate_slopes_greater_than':'1/3',
            'heldout_separation_greater_than':'1/10','heldout_vertices':heldout}
    print(json.dumps(result,indent=2))

if __name__=='__main__':check(sys.argv[1])
