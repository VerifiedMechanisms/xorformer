#!/usr/bin/env python3
"""Exact Laurent diagnostic for one H16 or H32 biased Haar target.

Run with heavy. This checks finite algebra only, not a density theorem.
All series divisions guard against exhausted precision, and every
intermediate kernel basis satisfies the exact block-bias relations.
The output records leading coefficients, not numerical approximations.
"""
from fractions import Fraction as F
from flint import fmpq_mat, fmpq_series as S, ctx
import importlib.util,json,sys,time
spec=importlib.util.spec_from_file_location('bf',str(__import__('pathlib').Path(__file__).resolve().parent/'butterfly-rectangle-decoder-check.py'))
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)
d=int(sys.argv[1]) if len(sys.argv)>1 else 4;H=1<<d
if d==4:
 bits=[1,0,0,0,1,1,0,1,1,1,0,1,1,1,1,1,0,0,0,0,1,1,1,1,0,0,0,1,1,1,1,0]
else:bits=json.load(open(str(__import__('pathlib').Path(__file__).resolve().parent/'butterfly-adaptive-haar-h32-sample.json')))['witnesses'][0]['bits']
sw=bf.switches(d);blocks=list(dict.fromkeys((k,g) for k,s,g in sw));q=len(sw);n=H+len(blocks)
pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)]
p=[sum((F(1,100)**(2**j) for j in range(d) if y&(1<<j)),F(0)) for y in range(H)]
def rows(p,zero,one):
 return [[((1-2*bits[e])*(0 if inv[y]>>(k+1)!=g else 1-2*((inv[y]>>k)&1)))/(one-p[s]-p[y]) for y in range(H)]+[one*(1-2*bits[e]) if b==(k,g) else zero for b in blocks] for e,(k,s,g) in enumerate(sw)]
A=rows(p,F(0),F(1)); At=fmpq_mat([[str(A[i][j]) for i in range(q)] for j in range(n)])
reduced,rank=At.rref(); rb=[]
for i in range(rank):rb.append(next(j for j in range(q) if reduced[i,j]))
Bt=fmpq_mat([[str(A[i][j]) for j in range(n)] for i in rb]); br,rank2=Bt.rref(); assert rank2==rank
cb=[next(j for j in range(n) if br[i,j]) for i in range(rank)]
rest=[i for i in range(q) if i not in rb]
print(json.dumps(dict(d=d,bits=bits,rank=rank,queries=q,variables=n,basis=rb,rest=rest)),flush=True)
K=1024;ctx.cap=K;x=S([0,1]);zero=S([]);one=S([1]);shift=K//3
p=[sum((x**(2**j) for j in range(d) if y&(1<<j)),zero) for y in range(H)];AF=rows(p,zero,one)
# Solve transpose of square basis, all nonbasis rows as simultaneous RHS.
B=[[AF[rb[j]][cb[i]] for j in range(rank)]+[x**shift*AF[e][cb[i]] for e in rest] for i in range(rank)]
columns=list(range(rank));piv=[]
for k in range(rank):
 cand=[(B[i][j].valuation(),i,j) for i in range(k,rank) for j in range(k,rank) if B[i][j].valuation()>=0]
 val,i,j=min(cand); assert min(v.prec for row in B for v in row)>val,(k,val,"insufficient solve precision"); piv.append(val);B[k],B[i]=B[i],B[k]
 for row in B:row[k],row[j]=row[j],row[k]
 columns[k],columns[j]=columns[j],columns[k]
 pivot=B[k][k];B[k]=[v/pivot for v in B[k]]
 for i in range(rank):
  if i!=k:
   mul=B[i][k];B[i]=[v-mul*w for v,w in zip(B[i],B[k])]
out=[]; kernel=[]
for t,e in enumerate(rest):
 coeff=[zero]*rank
 for k in range(rank):coeff[columns[k]]=B[k][rank+t]
 for j in range(n):
  res=sum((coeff[i]*AF[rb[i]][j] for i in range(rank)),zero)-x**shift*AF[e][j]
  assert res.valuation()<0, (e,j,str(res))
 lead=[]
 for i,v in enumerate(coeff):
  z=v.valuation()
  if z>=0:lead.append([rb[i],z-shift,str(-v[z])])
 lead.append([e,0,'1']);out.append(dict(row=e,leading_circuit=lead))
 ker=[zero]*q
 for i,v in enumerate(coeff):ker[rb[i]]=-v
 ker[e]=x**shift;kernel.append(ker)
# Valuation-normalized elimination of the circuit space.
kernel=[[v/(x**min(w.valuation() for w in row if w.valuation()>=0)) for v in row] for row in kernel]
print(json.dumps(dict(kernel_precision=min(v.prec for row in kernel for v in row))),file=sys.stderr,flush=True)
def audit_kernel(label):
 for rr,row in enumerate(kernel):
  for block in blocks:
   val=sum((row[j]*(1-2*bits[j]) for j,e in enumerate(sw) if (e[0],e[2])==block),zero)
   assert val.valuation()<0,(label,rr,block,str(val))
audit_kernel('initial')
kpiv=[]
for k in range(len(kernel)):
 best=min((v.valuation(),i,j) for i in range(k,len(kernel)) for j,v in enumerate(kernel[i]) if v.valuation()>=0)
 val,i,j=best; assert min(v.prec for row in kernel[k:] for v in row)>val,(k,val,"insufficient precision"); kernel[k],kernel[i]=kernel[i],kernel[k]
 pivot=kernel[k][j];kernel[k]=[v/pivot for v in kernel[k]]
 kpiv.append(j)
 for i in range(len(kernel)):
  if i!=k:
   mul=kernel[i][j];kernel[i]=[v-mul*w for v,w in zip(kernel[i],kernel[k])]

 audit_kernel(k)
print(json.dumps(dict(flag_precision=min(v.prec for row in kernel for v in row))),file=sys.stderr,flush=True)
audit_kernel('final')
flag=[]
for row in kernel:
 lead=[]
 for j,v in enumerate(row):
  z=v.valuation()
  if z>=0:lead.append([j,z,str(v[z])])
 flag.append(lead)
print(json.dumps(dict(pivots=piv,circuits=out,kernel_pivots=kpiv,kernel_flag=flag),indent=2),flush=True)
