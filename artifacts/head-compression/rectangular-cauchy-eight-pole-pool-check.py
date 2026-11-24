#!/usr/bin/env python3
"""Exact finite and guarded Laurent check of the eight-pole shared pool.
Requires python-flint. No optimizer, numerical tolerance, or guessed signs.
"""
import itertools,json
from fractions import Fraction as F
from pathlib import Path
from flint import fmpq_series as S,fmpq,ctx
path=Path(__file__).with_name('rectangular-cauchy-eight-pole-pool.json')
d=json.loads(path.read_text());q=4;H=8;t=list(map(F,d['t']));p=list(map(F,d['p']));v=list(map(F,d['v']))
assert t==[F(77,80),F(39,40),F(79,80),F(1)]
assert all(p[h]==(h+1)*p[0] for h in range(H)) and min(v)>0
for a,b,c,e in itertools.product([-1,1],repeat=4):
 tau=[a,b,c,e,-c,c,-a,a];word=[e,-a,b,c]
 for j in range(q):assert word[j]*sum(tau[h]*v[h]/(t[j]-p[h]) for h in range(H))>0
ctx.cap=d['precision'];x=S([0,1]);M=d['shift'];rows=[];tags=[]
for a,w in enumerate(d['witnesses']):
 for j in range(q):
  rows.append([w['word'][j]*w['tau'][h]/(S([fmpq(str(t[j]))])-x*(h+1)) for h in range(H)]);tags.append([a,j])
for h in range(H):rows.append([S([int(h==j)]) for j in range(H)]);tags.append([-1,h])
basis=[tags.index(z) for z in d['basis']];T=[rows[i][:]+[x**M] for i in basis];cols=list(range(H));pivots=[]
for k in range(H):
 val,i,j=min((T[i][j].valuation(),i,j) for i in range(k,H) for j in range(k,H) if T[i][j].valuation()>=0)
 assert all(T[ii][jj].valuation()>=0 or T[ii][jj].prec>=val for ii in range(k,H) for jj in range(k,H))
 pivots.append(val);T[k],T[i]=T[i],T[k]
 for row in T:row[k],row[j]=row[j],row[k]
 cols[k],cols[j]=cols[j],cols[k];pivot=T[k][k];T[k]=[z/pivot for z in T[k]]
 for i in range(H):
  if i!=k:
   multiplier=T[i][k]
   # An unknown zero still propagates its precision loss.
   T[i]=[a-multiplier*b for a,b in zip(T[i],T[k])]
c=[None]*H
for k in range(H):c[cols[k]]=T[k][-1]
assert pivots==d['pivots']
for i in basis:
 z=sum((a*b for a,b in zip(rows[i],c)),S([]))-x**M
 assert z.valuation()<0 and z.prec>0
leading=[]
for tag,row in zip(tags,rows):
 z=sum((a*b for a,b in zip(row,c)),S([]));val=z.valuation()
 assert val>=0 and z[val]>0
 leading.append([tag,val-M,str(z[val])])
assert leading==d['leading']
for saved in d['grouped']:
 a,b,cc,e=saved['code'];tau=[a,b,cc,e,-cc,cc,-a,a];word=[e,-a,b,cc]
 assert tau==saved['tau'] and word==saved['word']
 for j in range(q):
  z=word[j]*sum((tau[h]*c[h]/(S([fmpq(str(t[j]))])-x*(h+1)) for h in range(H)),S([]))
  val=z.valuation();assert val>=0 and z[val]>0
  assert [val-M,str(z[val])]==saved['leading'][j]
print('PASS: all 16 grouped words, finite rational and all-small-epsilon; eight positive residues; every series precision audited.')
