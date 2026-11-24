#!/usr/bin/env python3
"""Independent exact-rational audit of the complete affine-plane head formulas.

This supplements the Lean proof by separately implementing the rank heads,
Cauchy corrections, strictification, axis repair, center reversal, and actual
fractional-atom normalization. Every 4 by 2 Boolean table is tested at q=2;
q=4 cases test restricted row embeddings and empty dimensions. This is a
finite diagnostic, not a proof of the universal or asymptotic theorem.

Requires SymPy. Run with the repository's ``heavy python3`` wrapper when
available on a shared machine. All tested equalities use exact rationals.
"""

from fractions import Fraction as F
from dataclasses import dataclass
from itertools import product
import random, json
import sympy as sp

@dataclass(frozen=True)
class Ratio:
    a0: F
    a: tuple
    b0: F
    b: tuple
    def value(self, x):
        return (self.a0 + sum((v*t for v,t in zip(self.a,x)),F(0))) / (self.b0 + sum((v*t for v,t in zip(self.b,x)),F(0)))
    def strictify(self):
        margin=self.b0+sum(self.b,F(0))
        assert margin>0 and all(t<=0 for t in self.b)
        eps=margin/F(len(self.b)+1)
        return Ratio(self.a0,self.a,self.b0+2*eps,tuple(t-eps for t in self.b))
    def check(self, strict=True):
        assert self.b0+sum(self.b,F(0))>0
        assert all(t<0 if strict else t<=0 for t in self.b)

def field_mul(a,b,q):
    polynomial={2:0b11,4:0b111,8:0b1011}[q]
    result=0
    while b:
        if b&1: result^=a
        b>>=1; a<<=1
        if a&q:a^=polynomial
    return result

def field_inv(a,q):
    return next(b for b in range(1,q) if field_mul(a,b,q)==1)

def make(k,r,s,table,seed):
    q=2**k; points=list(product(range(q),repeat=2))
    allrows=list(product(points,range(k)))
    rng=random.Random(seed); rng.shuffle(allrows); rows=allrows[:r]
    full={(h,b,j):rng.randrange(2) for h in points for b in range(k) for j in range(s)}
    for i,(h,b) in enumerate(rows):
        for j in range(s):full[h,b,j]=table[i][j]
    memory={(h,j):sum(full[h,b,j]<<b for b in range(k)) for h in points for j in range(s)}
    delta=F(1,4*(r+s+1)); pole=[1-delta*F(a+1,q+1) for a in range(q)]; token=[delta*F(a+1,q+1) for a in range(q)]
    C=sp.Matrix([[sp.Rational(1/(pole[a]-token[z])) for a in range(q)] for z in range(q)])
    eta=[]
    for b in range(k):
        v=C.inv()*sp.Matrix([2*((z>>b)&1)-1 for z in range(q)])
        eta.append([F(c.p,c.q) for c in v])
    Z={(a,c,j):sum((1/(pole[a]-token[memory[g,j]]) for g in points if g[1]==(field_mul(a,g[0],q)^c)),F(0)) for a,c in points for j in range(s)}
    heads=[]; col=[F(0) for _ in range(s)]
    for a,c in points:
        f=[eta[b][a] if c==(h[1]^field_mul(a,h[0],q)) else F(0) for h,b in rows]
        g=[Z[a,c,j] for j in range(s)]
        C0=1+sum(map(abs,f),F(0)); M=4*(r+1)*C0; u=[C0+t for t in f]
        head=Ratio(F(0),tuple([F(0)]*r+[M*t for t in g]),F(1),tuple([-t/(M+t) for t in u]+[F(0)]*s))
        head.check(strict=False); heads.append(head.strictify())
        for j in range(s):col[j]-=(M+C0)*g[j]
    heads.append(Ratio(F(0),tuple([F(0)]*r+col),F(1),tuple([F(0)]*(r+s))).strictify())
    for g in points:
        A=[]; D=[]
        for h,b in rows:
            slope=field_mul(g[1]^h[1],field_inv(g[0]^h[0],q),q) if g[0]!=h[0] else 0
            A.append(-eta[b][slope] if g[0]!=h[0] else F(0));D.append(pole[slope])
        heads.append(Ratio(F(0),tuple(A+[F(0)]*s),F(1),tuple([t-1 for t in D]+[-token[memory[g,j]] for j in range(s)])))
    assert len(heads)==2*q*q+1
    for h in heads:h.check()
    return heads

def axis_repair(heads,r,s):
    out=[]; row=[F(0)]*r; col=[F(0)]*s
    for R in heads:
        t=max(R.b) if R.b else F(-1); kval=R.a0/R.b0
        a=[v-kval*b for v,b in zip(R.a,R.b)]
        out.append(Ratio(F(0),tuple(a),R.b0,R.b))
        out.append(Ratio(F(0),tuple([-v for v in a[:r]]+[F(0)]*s),R.b0,tuple(list(R.b[:r])+[t]*s)))
        out.append(Ratio(F(0),tuple([F(0)]*r+[-v for v in a[r:]]),R.b0,tuple([t]*r+list(R.b[r:]))))
        for i in range(r):row[i]+=kval+a[i]/(R.b0+R.b[i]+t)
        for j in range(s):col[j]+=a[r+j]/(R.b0+t+R.b[r+j])
    L=F(2*(r+s)+4); scale=(L-2)*(L-3)
    out.append(Ratio(F(0),tuple([scale*t for t in row]+[F(0)]*s),L,tuple([F(-1)]*r+[F(-2)]*s)))
    out.append(Ratio(F(0),tuple([F(0)]*r+[scale*t for t in col]),L,tuple([F(-2)]*r+[F(-1)]*s)))
    out.append(Ratio(F(0),tuple([-scale*t for t in row+col]),L,tuple([F(-1)]*(r+s))))
    assert len(out)==3*len(heads)+3
    for h in out:h.check()
    return out

counts={'tables':0,'grid_checks':0,'axis_checks':0,'full_cube_denominator_checks':0,'reversed_atom_checks':0}
def check_case(k,r,s,table,seed):
    raw=make(k,r,s,table,seed); repaired=axis_repair(raw,r,s)
    for i,j in product(range(r),range(s)):
        bits=tuple(int(t==i) for t in range(r))+tuple(int(t==j) for t in range(s))
        target=2*table[i][j]-1
        assert sum((h.value(bits) for h in raw),F(0))==target
        assert sum((h.value(bits) for h in repaired),F(0))==target
        counts['grid_checks']+=2
    for z in product(range(2),repeat=r):
        assert sum((h.value(z+(0,)*s) for h in repaired),F(0))==0; counts['axis_checks']+=1
    for w in product(range(2),repeat=s):
        assert sum((h.value((0,)*r+w) for h in repaired),F(0))==0; counts['axis_checks']+=1
    allbits=list(product(range(2),repeat=r+s))
    for h in raw+repaired:
        for bits in allbits:
            assert h.b0+sum((x*b for x,b in zip(bits,h.b)),F(0))>0
            counts['full_cube_denominator_checks']+=1
    # Test a real original-model atom after center reversal and localization.
    center=tuple(int((i+seed)%3!=0) for i in range(r+s)); penalty=F(3)
    for h in repaired:
        a0=h.a0+sum((c*a for c,a in zip(center,h.a)),F(0)); a=tuple(-v if c else F(0) for c,v in zip(center,h.a))
        b0=h.b0+sum((c*b for c,b in zip(center,h.b)),F(0)); b=tuple(-v if c else 1+penalty for c,v in zip(center,h.b))
        assert b0>0 and all(t>0 for t in b)
        scale=1+sum(b,F(0))/b0; rho=tuple(t/scale for t in b); alpha=1+scale
        gamma=b0-sum(rho,F(0)); m=tuple(x/y for x,y in zip(a,b)); eta=a0-sum((x*y for x,y in zip(rho,m)),F(0))
        assert gamma>0 and alpha>0 and all(x>0 for x in rho)
        for bits in allbits:
            weights=tuple(p*(alpha if x else 1) for p,x in zip(rho,bits))
            atom=(eta+sum((w*t for w,t in zip(weights,m)),F(0)))/(gamma+sum(weights,F(0)))
            affine=(a0+sum((t*x for t,x in zip(a,bits)),F(0)))/(b0+sum((t*x for t,x in zip(b,bits)),F(0)))
            assert atom==affine
            if all(x<=c for x,c in zip(bits,center)):
                local=tuple(c*(1-x) for c,x in zip(center,bits));assert atom==h.value(local)
            counts['reversed_atom_checks']+=1
    counts['tables']+=1

# Every possible table at the smallest complete affine-plane row capacity.
for code in range(2**8):
    table=[[(code>>(i*2+j))&1 for j in range(2)] for i in range(4)]
    check_case(1,4,2,table,code)
print(json.dumps({'stage':'exhaustive_q2','counts':counts},sort_keys=True),flush=True)
# Restricted rows, all-zero/all-one and random data, plus empty dimensions.
for r,s in [(0,0),(0,2),(2,0),(1,1),(3,2),(5,3)]:
    for seed in range(3):
        rng=random.Random(2026+seed)
        table=[[seed if seed<2 else rng.randrange(2) for j in range(s)] for i in range(r)]
        check_case(2,r,s,table,seed)
print(json.dumps({'stage':'final','counts':counts,'status':'passed'},sort_keys=True),flush=True)
