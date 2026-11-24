#!/usr/bin/env python3
"""Exact finite and Laurent obstruction to nonnegative unbiassed Haar residues.

Scope: the one displayed H16 target and fixed pole/query prescription.
Signed residues and block biases are not constrained by this certificate.
Requires python-flint. No feasibility solver is used.
"""
from pathlib import Path
from fractions import Fraction as F
import json,importlib.util,sys
from flint import fmpq_series as S,ctx
path=Path(__file__).parent
certificate=Path(sys.argv[1]) if len(sys.argv)>1 else path/'butterfly-adaptive-haar-positive-h16-dual.json'
data=json.loads(certificate.read_text())
K=data['precision'];ctx.cap=K;M=K//3;x=S([0,1]);d=data['dimension'];H=1<<d;bits=data['bits'];powers=data['powers']
spec=importlib.util.spec_from_file_location('bf',path/'butterfly-rectangle-decoder-check.py');bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf);sw=bf.switches(d);pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)]
# Independently verify the saved finite rational certificate.
epsilon=F(data['epsilon'])
finite_p=[sum((epsilon**powers[j] for j in range(d) if y&(1<<j)),F(0)) for y in range(H)]
finite_A=[[F((1-2*bits[e])*(0 if inv[y]>>(k+1)!=g else 1 if not inv[y]&(1<<k) else -1))/(1-finite_p[s]-finite_p[y]) for y in range(H)] for e,(k,s,g) in enumerate(sw)]
finite_A += [[F(i==j) for j in range(H)] for i in range(H)]
finite_lambda=[F(0)]*len(finite_A)
for index,value in data['dual']:finite_lambda[index]=F(value)
assert sum(finite_lambda)==1 and min(finite_lambda)>=0
assert sum(finite_lambda[:len(sw)])>0
assert all(sum(finite_lambda[i]*finite_A[i][j] for i in range(len(finite_A)))==0 for j in range(H))
# The normalized active dual system is rational in epsilon. The guarded
# series solve certifies its Laurent leading terms, not only residuals.
p=[sum((x**powers[j] for j in range(d) if y&(1<<j)),S([])) for y in range(H)]
A=[[S([]) if inv[y]>>(k+1)!=g else (1-2*bits[e])*(1 if not inv[y]&(1<<k) else -1)/(1-p[s]-p[y]) for y in range(H)] for e,(k,s,g) in enumerate(sw)]
A += [[S([int(i==j)]) for j in range(H)] for i in range(H)];support=[i for i,v in data['dual']];N=len(support);assert N==H+1
B=[[A[i][j] for i in support] for j in range(H)]+[[S([1])]*N];rhs=[S([])]*H+[x**M];orig=[r[:] for r in B];T=[r+[b] for r,b in zip(B,rhs)];cols=list(range(N));piv=[]
for k in range(N):
 can=[(T[i][j].valuation(),i,j) for i in range(k,N) for j in range(k,N) if T[i][j].valuation()>=0];assert can
 v,i,j=min(can);piv.append(v);assert all(T[ii][jj].valuation()>=0 or T[ii][jj].prec>=v for ii in range(k,N) for jj in range(k,N));T[i],T[k]=T[k],T[i]
 for row in T:row[j],row[k]=row[k],row[j]
 cols[j],cols[k]=cols[k],cols[j];pivot=T[k][k];assert all(z.prec>=v if z.valuation()<0 else z.valuation()>=v for z in T[k]);T[k]=[z/pivot for z in T[k]]
 for i in range(N):
  if i!=k:
   mult=T[i][k];T[i]=[a-mult*b for a,b in zip(T[i],T[k])]
sol=[None]*N
for i in range(N):sol[cols[i]]=T[i][-1]
for row,b in zip(orig,rhs):
 r=sum((a*c for a,c in zip(row,sol)),S([]))-b;assert r.valuation()<0 and r.prec>0
lead=[]
for i,z in zip(support,sol):
 v=z.valuation();assert v>=0;lead.append([i,v-M,str(z[v])]);assert z[v]>0,(i,v-M,str(z[v]))
result=dict(support=support,pivots=piv,leading=lead)
assert result==data['laurent']
print(json.dumps(dict(dimension=d,strict_query_rows=sum(i<len(sw) for i in support),nonnegative_residue_rows=sum(i>=len(sw) for i in support),positive_laurent_weights=len(lead),status='infeasible for every sufficiently small positive epsilon')))
