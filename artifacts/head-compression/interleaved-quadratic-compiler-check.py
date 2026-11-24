#!/usr/bin/env python3
"""Exact checks for the interleaved quadratic cone; no numerical solver."""
from fractions import Fraction as F
from itertools import product

def value(roots, first, x):
    out=F(first)
    for root in roots: out*=root-x
    return out

def witness(g, ysign, qsign):
    odd=(1,)+qsign
    choices=[]
    for phase in (1,-1):
        word=[]
        for j in range(g+1): word.extend((ysign[j],phase*odd[j]))
        word.append(ysign[-1])
        changes=[j for j in range(2*g+2) if word[j]!=word[j+1]]
        choices.append((changes,word))
    changes,word=min(choices,key=lambda z:len(z[0]))
    assert len(changes)<=g+1
    roots=[F(2*j+1,2) for j in changes]
    vals=[value(roots,word[0],j) for j in range(2*g+3)]
    assert all(v*s>0 for v,s in zip(vals,word))
    yy=vals[::2]; tt=vals[1::2]
    assert all(v*s>0 for v,s in zip(yy,ysign))
    assert all(tt[0]*tt[j+1]*qsign[j]>0 for j in range(g))
    return yy,tt

count=0
for g in range(1,6):
    for word in product((-1,1),repeat=2*g+2):
        witness(g,word[:g+2],word[g+2:]); count+=1
    H=g+1; eta=F(1,1000*H); a=[F(1)]*g+[F(-g)]
    ww=[]; vv=[]
    for l in range(g):
        w=[F(1)]*H;w[l]+=eta;w[-1]+=eta/g
        assert sum(x*y for x,y in zip(a,w))==0
        ww.append(w);vv.append([x*y*y for x,y in zip(a,w)])
    for l in range(g):
        for k in range(g):
            expected=[F(0)]*H
            expected[l]+=2*eta+eta*eta;expected[k]-=2*eta+eta*eta
            assert [x-y for x,y in zip(vv[l],vv[k])]==expected
    # Verify the two prescribed pair signs from the exact leading expression.
    kap=F(1001,1000); mid=(1+kap)/2
    for q,s2 in product((-1,1),repeat=2):
        x=F(0) if q==s2 else -F(q)/mid
        assert (q+x)*q>0 and (q+kap*x)*s2>0
print(f'PASS: {count} exact cone words, all rank identities and paired leading signs')
