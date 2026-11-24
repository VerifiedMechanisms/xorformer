#!/usr/bin/env python3
"""Exact compact primal continuation for one original H32 Haar target.

Requires python-flint. Run with heavy. This verifies one target for all
sufficiently small positive epsilon, not a universal Haar decoder.
"""
import importlib.util,json,time,sys
from pathlib import Path
from flint import fmpq_series as S,ctx
HERE=Path(__file__).resolve().parent
start=time.time();ctx.cap=1600;BPOW=256
sp=importlib.util.spec_from_file_location('x',str(HERE/'butterfly-paired-offset-check.py'));x=importlib.util.module_from_spec(sp);sp.loader.exec_module(x)
data=json.loads((HERE/'joint-family-haar-h32-compact-germ.json').read_text());d=data['d'];H=1<<d;bits=data['bits'];active=data['active'];scalecol=data['scalecol'];scalesign=data['scalesign'];_,labels=x.reduced_rows(d,bits,'haar')
z=S([]);one=S([1]);eps=S([0,1]);gamma=[eps**(2**j)for j in range(d)];p=[sum((gamma[j]for j in range(d)if y&(1<<j)),z)for y in range(H)];pi=x.bf.permutation(d,bits);inv=[pi.index(y)for y in range(H)]
cache={}
def value(k,g,s):
 key=k,g,s
 if key in cache:return cache[key]
 t=one-p[s];gg=gamma[k]
 a=[x.mask(inv[y],k,g,'haar')*gg/((t-p[y])*(t+gg-p[y]))for y in range(H)]
 b=gg*sum((x.mask(inv[y],k,g,'haar')*(one/(t-p[y])+one/(t+gg-p[y]))for y in range(H)),z)
 cache[key]=a+[b];return cache[key]
rows=[]
for k,g,s,t in labels:rows.append([v-w for v,w in zip(value(k,g,s),value(k,g,t))])
rows.extend([[z]*H+[one],[one]+[z]*H]);n=H+1
mat=[]
for idx,col,sgn in zip(active,scalecol,scalesign):
 rhs=(eps**BPOW)*sgn*rows[idx][col]
 mat.append(rows[idx]+[rhs if idx!=len(rows)-1 else z,rhs if idx==len(rows)-1 else z])
perm=list(range(n));piv=[]
for k in range(n):
 val,i,j=min((mat[i][j].valuation(),i,j)for i in range(k,n)for j in range(k,n)if mat[i][j].valuation()>=0)
 prec=min(a.prec for row in mat for a in row);assert prec>val
 piv.append([val,str(mat[i][j][val])]);mat[k],mat[i]=mat[i],mat[k]
 for row in mat:row[k],row[j]=row[j],row[k]
 perm[k],perm[j]=perm[j],perm[k];pv=mat[k][k];mat[k]=[a/pv for a in mat[k]]
 for i in range(n):
  if i!=k:
   c=mat[i][k]
   if c.valuation()>=0:mat[i]=[a-c*b for a,b in zip(mat[i],mat[k])]
 print('pivot',k,'valuation',val,'precision',prec,'seconds',round(time.time()-start,2),flush=True)
u=[z]*n;v=[z]*n
for k in range(n):u[perm[k]]=mat[k][-2];v[perm[k]]=mat[k][-1]
def rescale(v):
 shift=min(a.valuation()for a in v if a.valuation()>=0)
 return [S(a.coeffs()[shift:],prec=a.prec-shift)for a in v],shift
u,ushift=rescale(u);v,vshift=rescale(v)
print('shifts',ushift,vshift,flush=True)
m=[sum((a*b for a,b in zip(row,u)),z)for row in rows[:-1]]
r=[sum((a*b for a,b in zip(row,v)),z)for row in rows[:-1]]
lo=data['lower'];hi=data['upper']
assert r[lo][r[lo].valuation()]>0 and r[hi][r[hi].valuation()]<0
coef_u=-2*r[lo]*r[hi];coef_v=m[lo]*r[hi]+m[hi]*r[lo]
w=[coef_u*a+coef_v*b for a,b in zip(u,v)];w,wshift=rescale(w)
margins=[sum((a*b for a,b in zip(row,w)),z)for row in rows[:-1]]
lead=[]
for i,a in enumerate(margins):
 val=a.valuation();lead.append([i,val,str(a[val])if val>=0 else '0',a.prec]);
 assert val>=0 and a[val]>0,('nonpositive margin',lead[-1])
out=dict(d=d,bits=bits,active=active,scalecol=scalecol,scalesign=scalesign,lower=lo,upper=hi,pivots=piv,ushift=ushift,vshift=vshift,wshift=wshift,margin_leading=lead,precision=min(a.prec for a in w+margins))
assert out==data, 'saved exact leading-term certificate differs'
print('positive',sum(a.valuation()>=0 and a[a.valuation()]>0 for a in margins),'total',len(margins),'precision',out['precision'],'seconds',round(time.time()-start,2),flush=True)
