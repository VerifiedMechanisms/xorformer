#!/usr/bin/env python3
"""Independent exact reconstruction of affine-plane heads, not just line sums.

Uses python-flint rationals. No upstream audit code is imported. The proof of
universality is the finite-field incidence identity in the accompanying note.
"""
from dataclasses import dataclass
from itertools import product
from random import Random
from flint import fmpq as Q, fmpq_mat


@dataclass
class Head:
    a0: Q
    a: list
    b0: Q
    b: list

    def minimum(self):
        return self.b0 + sum((min(Q(0), x) for x in self.b), Q(0))

    def strict(self):
        m = self.minimum()
        assert m > 0 and all(x <= 0 for x in self.b)
        e = m / (len(self.b) + 1)
        out = Head(self.a0, self.a[:], self.b0 + 2*e, [x-e for x in self.b])
        assert out.minimum() > 0 and all(x < 0 for x in out.b)
        return out

    def value(self, ones):
        d = self.b0 + sum((self.b[i] for i in ones), Q(0))
        assert d > 0
        return (self.a0 + sum((self.a[i] for i in ones), Q(0))) / d


def field(k):
    modulus = {1: 0b11, 2: 0b111, 3: 0b1011}[k]
    q = 1 << k
    def mul(a,b):
        c=0
        while b:
            if b&1: c ^= a
            b >>= 1
            a <<= 1
            if a&q: a ^= modulus
        return c
    def inverse(a):
        assert a
        return next(b for b in range(1,q) if mul(a,b)==1)
    assert all(mul(a,inverse(a))==1 for a in range(1,q))
    return q,mul,inverse


def axisize(heads,r,s):
    repaired=[]; rows=[Q(0)]*r; cols=[Q(0)]*s
    for h in heads:
        t=max(h.b); constant=h.a0/h.b0
        a=[x-constant*y for x,y in zip(h.a,h.b)]
        repaired += [Head(Q(0),a,h.b0,h.b[:]),
                     Head(Q(0),[-x for x in a[:r]]+[Q(0)]*s,h.b0,h.b[:r]+[t]*s),
                     Head(Q(0),[Q(0)]*r+[-x for x in a[r:]],h.b0,[t]*r+h.b[r:])]
        for i in range(r): rows[i] += constant+a[i]/(h.b0+h.b[i]+t)
        for j in range(s): cols[j] += a[r+j]/(h.b0+t+h.b[r+j])
    L=Q(2*(r+s)+4); scale=(L-2)*(L-3)
    repaired += [Head(Q(0),[scale*x for x in rows]+[Q(0)]*s,L,[Q(-1)]*r+[Q(-2)]*s),
                 Head(Q(0),[Q(0)]*r+[scale*x for x in cols],L,[Q(-2)]*r+[Q(-1)]*s),
                 Head(Q(0),[-scale*x for x in rows+cols],L,[Q(-1)]*(r+s))]
    assert len(repaired)==3*len(heads)+3
    assert all(h.minimum()>0 and all(x<0 for x in h.b) for h in repaired)
    return repaired


def check(k,r,s,repair):
    q,mul,inverse=field(k); points=list(product(range(q),repeat=2))
    allrows=[(h,b) for h in points for b in range(k)]
    rng=Random(71093+100*k+r+s)
    rng.shuffle(allrows)
    rows=allrows[:r]                    # deliberately non-initial embedding
    target=[[rng.choice([-1,1]) for j in range(s)] for i in range(r)]
    memory={(h,j):0 for h in points for j in range(s)}
    for i,(h,b) in enumerate(rows):
        for j in range(s):
            if target[i][j]==1: memory[h,j] |= 1<<b
    assert all((1 if memory[h,j]>>b&1 else -1)==target[i][j]
               for i,(h,b) in enumerate(rows) for j in range(s))
    eps=Q(1,4*(r+s+1)); poles=[1-eps*Q(a+1,q+1) for a in range(q)]
    tokens=[eps*Q(z+1,q+1) for z in range(q)]
    C=fmpq_mat([[1/(poles[a]-tokens[z]) for a in range(q)] for z in range(q)])
    Cinv=C.inv()
    eta=[]
    for b in range(k):
        word=fmpq_mat([[1 if z>>b&1 else -1] for z in range(q)])
        v=Cinv*word
        assert C*v==word
        eta.append([v[a,0] for a in range(q)])
    incidence=0
    for h in points:
        for g in points:
            common=[a for a in range(q) if g[1]==(mul(a,g[0])^h[1]^mul(a,h[0]))]
            if h==g: assert len(common)==q
            elif h[0]==g[0]: assert common==[]
            else: assert common==[mul(g[1]^h[1],inverse(g[0]^h[0]))]
            incidence += 1
    Z={}
    for a,c in points:
        for j in range(s):
            Z[a,c,j]=sum((1/(poles[a]-tokens[memory[g,j]])
                         for g in points if g[1]==(mul(a,g[0])^c)),Q(0))
    raw=[]; shared=[Q(0)]*s
    for a,c in points:
        f=[eta[b][a] if c==(h[1]^mul(a,h[0])) else Q(0) for h,b in rows]
        g=[Z[a,c,j] for j in range(s)]
        shift=1+sum(map(abs,f),Q(0)); M=4*(r+1)*shift
        u=[shift+x for x in f]
        raw.append(Head(Q(0),[Q(0)]*r+[M*x for x in g],Q(1),[-x/(M+x) for x in u]+[Q(0)]*s))
        for j in range(s): shared[j]-=(M+shift)*g[j]
    raw.append(Head(Q(0),[Q(0)]*r+shared,Q(1),[Q(0)]*(r+s)))
    for g in points:
        A=[]; D=[]
        for h,b in rows:
            if g[0]!=h[0]:
                a=mul(g[1]^h[1],inverse(g[0]^h[0])); A.append(-eta[b][a]); D.append(poles[a])
            else: A.append(Q(0)); D.append(poles[0])
        raw.append(Head(Q(0),A+[Q(0)]*s,Q(1),[x-1 for x in D]+[-tokens[memory[g,j]] for j in range(s)]))
        assert raw[-1].minimum()>Q(3,4)
    assert len(raw)==2*q*q+1
    heads=[h.strict() for h in raw]
    for i in range(r):
        for j in range(s):
            v=sum((h.value([i,r+j]) for h in heads),Q(0))
            assert v==target[i][j],(k,i,j,v,target[i][j])
    axes=0
    if repair:
        repaired=axisize(heads,r,s)
        for i in range(r):
            for j in range(s): assert sum((h.value([i,r+j]) for h in repaired),Q(0))==target[i][j]
        for block,offset in [(r,0),(s,r)]:
            masks=range(1<<block) if block<=10 else [rng.randrange(1<<block) for _ in range(40)]
            for mask in masks:
                ones=[offset+i for i in range(block) if mask>>i&1]
                assert sum((h.value(ones) for h in repaired),Q(0))==0
                axes += 1
        if r+s<=10:
            for mask in range(1<<(r+s)):
                ones=[i for i in range(r+s) if mask>>i&1]
                for h in repaired: h.value(ones)
    print(dict(q=q,rows=r,columns=s,incidence_pairs=incidence,strict_heads=len(heads),
               exact_grid_values=r*s,axis_heads=3*len(heads)+3 if repair else None,
               checked_axis_values=axes),flush=True)


if __name__=='__main__':
    check(1,4,3,True)
    check(2,27,9,True)
    check(3,187,5,False)
