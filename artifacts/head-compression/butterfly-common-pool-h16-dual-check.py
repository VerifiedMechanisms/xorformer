#!/usr/bin/env python3
"""Verify a 17-comparison obstruction to one common signed H16 residue pool.

Every comparison is reconstructed from an actual butterfly target. The
normalized positive dual is checked over rationals at the saved scale and
by guarded exact Laurent series near zero. No feasibility solver is used.
This does not obstruct target-adaptive residue vectors.
"""
from pathlib import Path
from fractions import Fraction as F
import json,sys,importlib.util
from flint import fmpq_series as S,ctx
here=Path(__file__).parent
D=json.load(open(sys.argv[1] if len(sys.argv)>1 else here/'butterfly-common-pool-h16-dual.json'));d=D['dimension'];H=1<<d;specs=D['rows'];J=len(specs);assert J==H+1;eps=F(D['epsilon']);p=[sum((eps**D['powers'][j] for j in range(d) if y&(1<<j)),F(0)) for y in range(H)]
sp=importlib.util.spec_from_file_location('bf',here/'butterfly-rectangle-decoder-check.py');bf=importlib.util.module_from_spec(sp);sp.loader.exec_module(bf);sw=bf.switches(d)
# Reconstruct one target for each comparison. Distinct tracked low-bit
# classes never compete in later layers, so their higher outputs can be set
# independently; the explicit permutation check below verifies the claim.
for a,b,u in specs:
 assert len(u)==H
 q=sum(v!=0 for v in u)//2;k=q.bit_length()-1;assert q==1<<k
 sg=1 if p[a]>p[b] else -1;bits=[0]*len(sw)
 for s in range(q):
  for bit in range(2):
   cls=[y for y in range(s+bit*q,H,2*q) if u[y]];assert len(cls)==1
   y=cls[0]
   if bit==0:
    sigma=sg*u[y];assert sigma in(-1,1);bits[sw.index((k,s,0))]=(1-sigma)//2
   else:assert u[y]==-sg*sigma
   for j in range(k+1,d):bits[sw.index((j,y% (1<<j),0))]=(y>>j)&1
 assert bits[sw.index((k,a,0))]==0 and bits[sw.index((k,b,0))]==1
 pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)]
 assert [sg*(0 if inv[y]>>(k+1) else 1 if not inv[y]&(1<<k) else -1) for y in range(H)]==u
rows=[[F(u[y])/((1-p[a]-p[y])*(1-p[b]-p[y])) for y in range(H)] for a,b,u in specs];lam=list(map(F,D['dual_weights']));assert all(v>0 for v in lam) and sum(lam)==1;assert all(sum(lam[i]*rows[i][y] for i in range(J))==0 for y in range(H))
# Solve the normalized dual over the formal Laurent field. All unknown
# truncated-zero multipliers are still propagated through elimination.
K=D.get('precision',1024);ctx.cap=K;M=K//3;x=S([0,1]);p=[sum((x**D['powers'][j] for j in range(d) if y&(1<<j)),S([])) for y in range(H)]
rows=[[u[y]/((1-p[a]-p[y])*(1-p[b]-p[y])) for y in range(H)] for a,b,u in specs];basis=[[rows[i][y] for i in range(J)] for y in range(H)]+[[S([1])]*J];rhs=[S([])]*H+[x**M];A=[r[:]+[b] for r,b in zip(basis,rhs)];cols=list(range(J));piv=[]
for k in range(J):
 v,i,j=min((A[i][j].valuation(),i,j) for i in range(k,J) for j in range(k,J) if A[i][j].valuation()>=0);piv.append(v);assert all(A[ii][jj].valuation()>=0 or A[ii][jj].prec>=v for ii in range(k,J) for jj in range(k,J));A[k],A[i]=A[i],A[k]
 for r in A:r[k],r[j]=r[j],r[k]
 cols[k],cols[j]=cols[j],cols[k];pivot=A[k][k];assert all(z.prec>=v if z.valuation()<0 else z.valuation()>=v for z in A[k]);A[k]=[z/pivot for z in A[k]]
 for i in range(J):
  if i!=k:
   mul=A[i][k];A[i]=[a-mul*b for a,b in zip(A[i],A[k])]
sol=[None]*J
for i in range(J):sol[cols[i]]=A[i][-1]
for r,b in zip(basis,rhs):
 res=sum((a*c for a,c in zip(r,sol)),S([]))-b;assert res.valuation()<0 and res.prec>0
lead=[]
for z in sol:
 v=z.valuation();assert v>=0 and z[v]>0;lead.append([v-M,str(z[v])])
print(json.dumps(dict(rows=J,pivots=piv,leading=lead,status='finite and small-epsilon common-pool obstruction, not adaptive-pool obstruction')))
