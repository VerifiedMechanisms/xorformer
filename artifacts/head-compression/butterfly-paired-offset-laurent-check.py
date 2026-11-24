#!/usr/bin/env python3
"""Exact rational-series Farkas continuation for the fixed H16 left-mask family.
Run with heavy. No global-model obstruction is asserted.
"""
import importlib.util,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
from fractions import Fraction as F
from flint import fmpq_mat, fmpq_series as S,ctx
sp=importlib.util.spec_from_file_location('x',str(HERE/'butterfly-paired-offset-check.py'));x=importlib.util.module_from_spec(sp);sp.loader.exec_module(x)
data=json.load(open(HERE/'butterfly-paired-offset-h16-dual.json'));d=data['d'];H=1<<d;bits=data['bits'];rows,labels=x.reduced_rows(d,bits);support=[i for i,a in enumerate(data['lambda'])if F(a)>0];n=len(support)
# columns whose transpose rows give independent equations
At=fmpq_mat([[str(rows[i][j])for j in range(H)]for i in support]);red,rank=At.rref();cb=[next(j for j in range(H)if red[i,j])for i in range(rank)];assert rank==n-1
free=support.index(max(support,key=lambda i:F(data['lambda'][i])));print('support',support,'columns',cb,'free',free,flush=True)
ctx.cap=512;z=S([]);one=S([1]);eps=S([0,1]);gamma=[eps**(2**j)for j in range(d)];p=[sum((gamma[j]for j in range(d)if y&(1<<j)),z)for y in range(H)];pi=x.bf.permutation(d,bits);inv=[pi.index(y)for y in range(H)]
def value(k,g,s):
 t=one-p[s];gg=gamma[k]
 a=[x.mask(inv[y],k,g,'left')*gg/((t-p[y])*(t+gg-p[y]))for y in range(H)]
 b=gg*sum((x.mask(inv[y],k,g,'left')*(one/(t-p[y])+one/(t+gg-p[y]))for y in range(H)),z)
 return a+[b]
SR=[]
for i in support:
 k,g,s,t=labels[i];a=value(k,g,s);b=value(k,g,t);SR.append([v-w for v,w in zip(a,b)])
unknown=[i for i in range(n)if i!=free];B=[[SR[i][j]for i in unknown]+[-SR[free][j]]for j in cb];perm=list(range(n-1));piv=[]
for k in range(n-1):
 v,i,j=min((B[i][j].valuation(),i,j)for i in range(k,n-1)for j in range(k,n-1)if B[i][j].valuation()>=0)
 assert min(a.prec for row in B for a in row)>v
 piv.append([v,str(B[i][j][v])]);B[k],B[i]=B[i],B[k]
 for row in B:row[k],row[j]=row[j],row[k]
 perm[k],perm[j]=perm[j],perm[k];pv=B[k][k];B[k]=[a/pv for a in B[k]]
 for i in range(n-1):
  if i!=k:
   c=B[i][k];B[i]=[a-c*b for a,b in zip(B[i],B[k])]
lam=[z]*n;lam[free]=one
for k in range(n-1):lam[unknown[perm[k]]]=B[k][-1]
for j in range(H):
 res=sum((lam[i]*SR[i][j]for i in range(n)),z);assert res.valuation()<0,(j,str(res))
lead=[]
for i,a in enumerate(lam):
 v=a.valuation();assert v>=0 and a[v]>0,(i,str(a));lead.append([support[i],v,str(a[v])])
bb=sum((lam[i]*SR[i][-1]for i in range(n)),z);v=bb.valuation();assert v>=0 and bb[v]<0,str(bb)
out=dict(d=d,bits=bits,support=support,columns=cb,free=free,pivots=piv,lambda_leading=lead,affine_leading=[v,str(bb[v])],precision=min(a.prec for a in lam+[bb]));print(json.dumps(out,indent=2),flush=True)
dest=HERE/'butterfly-paired-offset-h16-laurent.json'
if '--write' in sys.argv:dest.write_text(json.dumps(out,indent=2)+'\n')
else:assert json.loads(dest.read_text())==out
print('exact Laurent certificate verified')
