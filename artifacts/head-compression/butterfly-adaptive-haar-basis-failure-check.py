#!/usr/bin/env python3
"""Check failure of one H64 active basis to continue to small epsilon.

This is NOT an infeasibility certificate for the target. It proves only
that the specified rational-function vertex has a negative query score.
Requires python-flint; run through heavy (about twenty minutes).
"""
from pathlib import Path
import json,importlib.util,sys
from flint import fmpq_series as S,ctx
K=int(sys.argv[2]) if len(sys.argv)>2 else 1280;ctx.cap=K;M=160;x=S([0,1]);data=json.load(open(sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name('butterfly-adaptive-haar-h64-basis-failure.json')));d=data['dimension'];H=1<<d;bits=data['bits'];powers=data['powers']
sp=importlib.util.spec_from_file_location('bf',Path(__file__).with_name('butterfly-rectangle-decoder-check.py'));bf=importlib.util.module_from_spec(sp);sp.loader.exec_module(bf);sw=bf.switches(d);pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)];blocks=list(dict.fromkeys((k,g) for k,s,g in sw));mixed=[b for b in blocks if len({bits[i] for i,(k,s,g) in enumerate(sw) if(k,g)==b})==2];erows=[(e,query) for e,query in enumerate(sw) if(query[0],query[2]) in mixed];p=[sum((x**powers[j] for j in range(d) if y&(1<<j)),S([])) for y in range(H)]
base={};pairs=[]
for ix in data['basis_rows']:
 e,(k,s,g)=erows[ix]
 if(k,g)not in base:base[k,g]=(e,s)
 else:pairs.append((e,k,s,g,*base[k,g]))
assert len(base)==len(mixed) and len(pairs)==H
B=[];rhs=[]
for e,k,s,g,e0,s0 in pairs:
 B.append([S([]) if inv[y]>>(k+1)!=g else (1 if not inv[y]&(1<<k) else -1)/((1-p[s]-p[y])*(1-p[s0]-p[y])) for y in range(H)])
 rhs.append(x**M*((1-2*bits[e])-(1-2*bits[e0]))/(p[s]-p[s0]))
T=[row[:]+[b] for row,b in zip(B,rhs)];cols=list(range(H));piv=[]
for k in range(H):
 can=[(T[i][j].valuation(),i,j) for i in range(k,H) for j in range(k,H) if T[i][j].valuation()>=0];assert can
 v,i,j=min(can);piv.append(v)
 if k%8==0:print('pivot',k,'valuation',v,flush=True,file=sys.stderr)
 assert all(T[ii][jj].valuation()>=0 or T[ii][jj].prec>=v for ii in range(k,H) for jj in range(k,H));T[i],T[k]=T[k],T[i]
 for row in T:row[j],row[k]=row[k],row[j]
 cols[j],cols[k]=cols[k],cols[j];pivot=T[k][k];assert all(z.prec>=v if z.valuation()<0 else z.valuation()>=v for z in T[k]);T[k]=[S([]) if j<k else S([1]) if j==k else z/pivot for j,z in enumerate(T[k])]
 for i in range(k+1,H):
  if i!=k:
   mult=T[i][k];T[i]=[S([]) if j<=k else a-mult*b for j,(a,b) in enumerate(zip(T[i],T[k]))]
print("pivot valuations",piv,"sum",sum(piv),"minimum matrix precision",min(z.prec for row in T for z in row),flush=True,file=sys.stderr)
temp=[S([]) for _ in range(H)]
for i in range(H-1,-1,-1):
 temp[i]=T[i][-1]-sum((T[i][j]*temp[j] for j in range(i+1,H)),S([]))
sol=[None]*H
for i in range(H):sol[cols[i]]=temp[i]
print("solution precision",min(z.prec for z in sol),"valuation",min((z.valuation() for z in sol if z.valuation()>=0),default=-1),flush=True,file=sys.stderr)
for row,b in zip(B,rhs):
 r=sum((a*c for a,c in zip(row,sol)),S([]))-b;assert r.valuation()<0 and r.prec>0
lead=[]
for z in sol:
 v=z.valuation();lead.append(None if v<0 else[v-M,str(z[v])])
def score(k,s,g):return sum(((1 if not inv[y]&(1<<k) else -1)*sol[y]/(1-p[s]-p[y]) for y in range(H) if inv[y]>>(k+1)==g),S([]))
bias={b:(1-2*bits[e0])*x**M-score(*((b[0],s0,b[1]))) for b,(e0,s0) in base.items()}
terms=[]
for ix,(e,(k,s,g)) in enumerate(erows):
 if ix!=data['failed_mixed_query']:continue
 e0,s0=base[k,g]
 diff=(p[s]-p[s0])*sum(((1 if not inv[y]&(1<<k) else -1)*sol[y]/((1-p[s]-p[y])*(1-p[s0]-p[y])) for y in range(H) if inv[y]>>(k+1)==g),S([]))
 z=(1-2*bits[e])*((1-2*bits[e0])*x**M+diff);v=z.valuation();assert v>=0,('undecided',ix);assert [v-M,str(z[v])]==data['failed_leading_term'];assert z[v]<0;terms.append([v-M,str(z[v]),z.prec-M])
print(json.dumps(dict(dimension=d,pivots=piv,failed_mixed_query=data['failed_mixed_query'],failed_leading_term=terms[0],scope='This active basis only; no target infeasibility assertion'),indent=2))
