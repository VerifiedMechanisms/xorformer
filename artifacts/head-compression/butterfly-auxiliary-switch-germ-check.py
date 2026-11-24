#!/usr/bin/env python3
"""Exact auxiliary-routing repair. Requires python-flint; no LP solver."""
import json,importlib.util
from pathlib import Path
from fractions import Fraction as F
from flint import fmpq_series as S,fmpq_mat,ctx
path=str(Path(__file__).resolve().parent)+'/'
dat=json.load(open(path+'butterfly-auxiliary-switch-germ.json'));d=dat['dimension'];H=1<<d;bits=dat['bits'];c=list(map(F,dat['residues']));powers=dat['powers'];eps=F(dat['epsilon'])
s=importlib.util.spec_from_file_location('bf',path+'butterfly-rectangle-decoder-check.py');bf=importlib.util.module_from_spec(s);s.loader.exec_module(bf);sw=bf.switches(d);pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)]
def rows(p,zero,one):
 A=[];tags=[]
 for e,(k,s,g) in enumerate(sw):
  if e==27:continue
  A.append([zero if inv[y]>>(k+1)!=g else (1-2*bits[e])*(1 if not inv[y]&(1<<k) else -1)/(one-p[s]-p[y]) for y in range(H)]);tags.append(e)
 A += [[one if i==j else zero for j in range(H)] for i in range(H)];tags+=list(range(32,48));return A,tags
p=[sum((eps**powers[j] for j in range(d) if y&(1<<j)),F(0)) for y in range(H)]
A,tags=rows(p,F(0),F(1));assert all(sum(a*b for a,b in zip(row,c))>=1 for row in A)
active=[i for i,row in enumerate(A) if sum(a*b for a,b in zip(row,c))==1];rr,rank=fmpq_mat([[str(A[i][j]) for i in active] for j in range(H)]).rref();assert rank==H
pivcols=[next(j for j in range(len(active)) if rr[i,j]) for i in range(H)];basis=[active[j] for j in pivcols];assert [tags[i] for i in basis]==dat['basis']
K=dat['precision'];M=K//3;ctx.cap=K;x=S([0,1]);pp=[sum((x**powers[j] for j in range(d) if y&(1<<j)),S([])) for y in range(H)];SA,_=rows(pp,S([]),S([1]));orig=[SA[i] for i in basis];T=[row[:]+[x**M] for row in orig];cols=list(range(H));pv=[]
for k in range(H):
 can=[(T[i][j].valuation(),i,j) for i in range(k,H) for j in range(k,H) if T[i][j].valuation()>=0];v,i,j=min(can);pv.append(v);assert all(T[ii][jj].valuation()>=0 or T[ii][jj].prec>=v for ii in range(k,H) for jj in range(k,H));T[k],T[i]=T[i],T[k]
 for row in T:row[k],row[j]=row[j],row[k]
 cols[k],cols[j]=cols[j],cols[k];piv=T[k][k];T[k]=[z/piv for z in T[k]]
 for i in range(H):
  if i!=k:
   m=T[i][k];T[i]=[a-m*b for a,b in zip(T[i],T[k])]
cs=[None]*H
for k in range(H):cs[cols[k]]=T[k][-1]
for row in orig:
 z=sum((a*b for a,b in zip(row,cs)),S([]))-x**M;assert z.valuation()<0 and z.prec>0
lead=[]
for tag,row in zip(tags,SA):
 z=sum((a*b for a,b in zip(row,cs)),S([]));v=z.valuation();lead.append([tag,v-M,str(z[v]) if v>=0 else None])
assert pv==dat['pivots'] and lead==dat['leading']
assert all(a is not None and F(a)>0 for i,v,a in lead)
old=json.load(open(path+'butterfly-adaptive-haar-positive-h16-dual.json'))
assert all(i!=27 for i,a in old['dual'])
assert [i for i,(a,b) in enumerate(zip(old['bits'],bits)) if a!=b]==[27]
print('PASS: 31 retained query signs and 16 positive residues, exact finite and all-small-epsilon germ; original dual omits the auxiliary query.')
