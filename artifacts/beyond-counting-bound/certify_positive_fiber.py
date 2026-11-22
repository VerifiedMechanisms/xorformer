#!/usr/bin/env python3
"""Produce and verify an exact contraction certificate for a positive fiber.

The verification path uses only integers, fractions, and JSON. The optional
preparation path uses mpmath solely to propose rational certificate data.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

class Interval:
    def __init__(self, lo, hi=None):
        self.lo=Q(lo); self.hi=Q(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self, other):
        other=as_interval(other)
        return Interval(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self, other):return self+-as_interval(other)
    def __rsub__(self, other):return as_interval(other)+-self
    def __mul__(self, other):
        other=as_interval(other)
        ends=[self.lo*other.lo,self.lo*other.hi,self.hi*other.lo,self.hi*other.hi]
        return Interval(min(ends),max(ends))
    __rmul__=__mul__
    def __truediv__(self, other):
        other=as_interval(other)
        assert other.lo>0 or other.hi<0
        return self*Interval(1/other.hi,1/other.lo)
    def __rtruediv__(self, other):return as_interval(other)/self
    def absmax(self):return max(abs(self.lo),abs(self.hi))

def as_interval(x):return x if isinstance(x,Interval) else Interval(x)

def bits(i,n):return [(i>>j)&1 for j in range(n)]

def score(p,x,n,h):
    return sum(sum(p[k*n+j]*x[j] for j in range(n))/(1+sum(p[h*n+k*n+j]*x[j] for j in range(n))) for k in range(h))

def jacobian(p,inputs,n,h):
    rows=[]
    for x in inputs:
        rowu=[];rowb=[]
        for k in range(h):
            a=sum(p[k*n+j]*x[j] for j in range(n))
            d=1+sum(p[h*n+k*n+j]*x[j] for j in range(n))
            rowu.extend(x[j]/d for j in range(n))
            rowb.extend(-a*x[j]/(d*d) for j in range(n))
        rows.append(rowu+rowb)
    return rows

def source_params(source):
    return [Q(v,source['scale']) for key in ('u_numerator','b_numerator') for row in source[key] for v in row]

def prepare(source,candidate,target):
    import mpmath as mp
    mp.mp.dps=100
    n,h=source['n'],source['heads'];d=2*n*h
    inputs=[bits(i,n) for i in source['indices']]
    sp=source_params(source)
    yq=[score(sp,x,n,h) for x in inputs]
    y=[mp.mpf(v.numerator)/v.denominator for v in yq]
    p=mp.matrix([mp.mpf(str(v)) for v in candidate['parameters']])
    for _ in range(8):
        residual=mp.matrix([score(p,x,n,h)-v for x,v in zip(inputs,y)])
        p-=mp.lu_solve(mp.matrix(jacobian(p,inputs,n,h)),residual)
    def rounded(v):return mp.nstr(v,85)
    center=[rounded(v) for v in p]
    c=mp.matrix([mp.mpf(v) for v in center])
    inv=mp.inverse(mp.matrix(jacobian(c,inputs,n,h)))
    source_mp=[mp.mpf(v.numerator)/v.denominator for v in sp]
    inv0=mp.inverse(mp.matrix(jacobian(source_mp,inputs,n,h)))
    cert=dict(source=source,center=center,radius='1e-30',
              inverse=[[rounded(inv[i,j]) for j in range(d)] for i in range(d)],
              source_inverse=[[rounded(inv0[i,j]) for j in range(d)] for i in range(d)])
    target.write_text(json.dumps(cert,indent=2)+'\n')

def verify(cert):
    source=cert['source'];n,h=source['n'],source['heads'];d=2*n*h
    assert len(source['indices'])==d and len(set(source['indices']))==d
    assert all(0<i<2**n for i in source['indices'])
    inputs=[bits(i,n) for i in source['indices']]
    sp=source_params(source);c=list(map(Q,cert['center']));r=Q(cert['radius'])
    assert len(c)==d and r>0
    matrix=lambda key:[[Q(v) for v in row] for row in cert[key]]
    R=matrix('inverse');R0=matrix('source_inverse')
    assert len(R)==len(R0)==d and all(len(row)==d for row in R+R0)
    box=[Interval(v-r,v+r) for v in c]
    assert all(v>0 for v in sp[h*n:]) and all(v.lo>0 for v in box[h*n:])
    J=jacobian(box,inputs,n,h)
    # ||I-R J(X)||_infinity bounds the derivative of T(z)=z-R F(z).
    contraction=max(sum((Interval(int(i==j))-sum(R[i][k]*J[k][j] for k in range(d))).absmax() for j in range(d)) for i in range(d))
    assert contraction<Q(1,2)
    residual=[score(c,x,n,h)-score(sp,x,n,h) for x in inputs]
    displacement=max(abs(sum(R[i][j]*residual[j] for j in range(d))) for i in range(d))
    assert displacement+contraction*r<r
    # The same norm criterion independently proves the source Jacobian invertible.
    J0=jacobian(sp,inputs,n,h)
    source_error=max(sum(abs(Q(int(i==j))-sum(R0[i][k]*J0[k][j] for k in range(d))) for j in range(d)) for i in range(d))
    assert source_error<Q(1,2)
    separated=[]
    for i in range(2**n):
        if i in source['indices'] or i==0:continue
        delta=score(box,bits(i,n),n,h)-score(sp,bits(i,n),n,h)
        if delta.lo>Q(1,10) or delta.hi<-Q(1,10):
            separated.append(dict(vertex=i,lower=str(delta.lo),upper=str(delta.hi)))
    assert separated
    assert all(c[i]+r<sp[i] or c[i]-r>sp[i] for i in [0])
    result=dict(status='VERIFIED',n=n,heads=h,matched_vertices=d+1,
                contraction_below='1/2',displacement_plus_contraction_radius_below_radius=True,
                source_inverse_error_below='1/2',all_slopes_strictly_positive=True,
                heldout_separation_exceeds='1/10',heldout_vertices=[v['vertex'] for v in separated],
                arithmetic='exact fractions; no floating point in verification')
    print(json.dumps(result,indent=2))
    return result

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('certificate',type=Path)
    ap.add_argument('--prepare-source',type=Path)
    ap.add_argument('--prepare-candidate',type=Path)
    args=ap.parse_args()
    if args.prepare_source:
        prepare(json.loads(args.prepare_source.read_text()),json.loads(args.prepare_candidate.read_text()),args.certificate)
    verify(json.loads(args.certificate.read_text()))

if __name__=='__main__':main()
