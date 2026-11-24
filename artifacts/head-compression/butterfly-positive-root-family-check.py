#!/usr/bin/env python3
"""Exact active-basis certificates in the antisymmetric positive-root family.

No optimization solver is used. Finite mode solves the supplied rational
basis and checks every positivity and mixed-child comparison. Laurent mode
uses exact rational series with guarded precision and proves continuation
on a punctured interval. The root signs follow from antisymmetry; finite
mode additionally checks them directly by partial fractions.
Requires python-flint. Run via heavy when verifying multiple certificates.
"""
import argparse, importlib.util, json, sys
from fractions import Fraction as F
from pathlib import Path
from flint import fmpq_mat, fmpq_series as Series, ctx
sys.set_int_max_str_digits(0)
parser=argparse.ArgumentParser();parser.add_argument('certificate');parser.add_argument('--laurent',action='store_true');parser.add_argument('--precision',type=int);parser.add_argument('--summary',action='store_true');args=parser.parse_args()
D=json.loads(Path(args.certificate).read_text());d=D['dimension'];H=1<<d;q=H//2;bits=D['bits'];powers=D['powers']
base=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('bf',base/'butterfly-rectangle-decoder-check.py');bf=importlib.util.module_from_spec(sp);sp.loader.exec_module(bf)
sw=bf.switches(d);pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)]
# Scale the barycentric map by a positive monomial so every entry is analytic.
if args.laurent:
 K=args.precision or D.get('precision',512);ctx.cap=K;x=Series([0,1]);one=Series([1]);zero=Series([]);M=K//4
 E=sum((1<<(d-1-j))*powers[j] for j in range(d))
 scale=x**E
else:x=F(D['epsilon']);one=F(1);zero=F(0);scale=one
p=[sum((x**powers[j] for j in range(d) if y&(1<<j)),zero) for y in range(H)];nodes=[z*(1-z) for z in p[:q]]
def div(a,b):
 if args.laurent:
  v=b.valuation();assert v>=0,'Unknown denominator';assert a.valuation()>=v or (a.valuation()<0 and a.prec>=v),'Insufficient series precision'
 return a/b
V=[]
for y in range(H):
 a=p[y]*(1-p[y]);u=1 if inv[y]<q else -1;qp=one
 for j in range(H):
  if j!=y:qp=qp*(p[y]-p[j])
 factor=div(scale*(p[y]-one/2),u*qp);row=[]
 for s in range(q):
  if y<q:lag=one if y==s else zero
  else:
   num=one;den=one
   for j in range(q):
    if j!=s:num=num*(a-nodes[j]);den=den*(nodes[s]-nodes[j])
   lag=div(num,den)
  row.append(factor*lag)
 V.append(row)
rows=list(V);specs=[]
for k,g in dict.fromkeys((k,g) for k,s,g in sw):
 if k==d-1:continue
 pos=[s for e,(l,s,b) in enumerate(sw) if(l,b)==(k,g) and bits[e]==0];neg=[s for e,(l,s,b) in enumerate(sw) if(l,b)==(k,g) and bits[e]==1]
 for a in pos:
  for b in neg:
   diff=p[a]-p[b]
   sg=(1 if diff[diff.valuation()]>0 else -1) if args.laurent else (1 if diff>0 else -1)
   r=[zero if inv[y]>>(k+1)!=g else sg*(1 if not inv[y]&(1<<k) else -1)/((1-p[a]-p[y])*(1-p[b]-p[y])) for y in range(H)]
   rows.append([sum((r[y]*V[y][s] for y in range(H)),zero) for s in range(q)]);specs.append((k,g,a,b))
assert len(rows)==D['constraints'];basis=D['basis'];assert len(basis)==q
if args.laurent:
 # The extra RHS monomial accommodates poles in the exact basis solution.
 A=[list(rows[i])+[x**M] for i in basis];columns=list(range(q));pivots=[]
 for k in range(q):
  options=[(A[i][j].valuation(),i,j) for i in range(k,q) for j in range(k,q) if A[i][j].valuation()>=0];assert options,'Increase precision'
  val,i,j=min(options);pivots.append(val)
  assert all(A[a][b].valuation()>=0 or A[a][b].prec>=val for a in range(k,q) for b in range(k,q))
  A[k],A[i]=A[i],A[k]
  for row in A:row[k],row[j]=row[j],row[k]
  columns[k],columns[j]=columns[j],columns[k];pivot=A[k][k]
  A[k]=[div(v,pivot) for v in A[k]]
  for i in range(q):
   if i!=k:
    # Never skip an unknown zero modulo tracked precision.
    mult=A[i][k];A[i]=[v-mult*w for v,w in zip(A[i],A[k])]
 values=[None]*q
 for k in range(q):values[columns[k]]=A[k][-1]
 for i in basis:
  residual=sum((a*b for a,b in zip(rows[i],values)),zero)-x**M
  assert residual.valuation()<0 and residual.prec>0
else:
 A=fmpq_mat([[str(v) for v in rows[i]] for i in basis]);b=A.inv()*fmpq_mat([[1] for _ in basis]);values=[F(str(b[i,0])) for i in range(q)]
scores=[sum((a*b for a,b in zip(r,values)),zero) for r in rows]
if args.laurent:
 leading=[]
 for s in scores:
  v=s.valuation();assert v>=0 and s[v]>0,'Nonpositive or undecided score';leading.append([v-M,str(s[v]),s.prec-M])
 if 'leading_residues' in D:assert [v[:2] for v in leading[:H]]==D['leading_residues']
 out=dict(dimension=d,constraints=len(rows),pivots=pivots,residue_leading=leading[:H],comparison_leading=None if args.summary else leading[H:])
else:
 assert min(scores)>=1
 c=scores[:H]
 for e,(k,s,g) in enumerate(sw):
  if k!=d-1:continue
  score=sum((F(1 if inv[y]<q else -1)*c[y]/(1-p[s]-p[y]) for y in range(H)),F(0))
  assert (1-2*bits[e])*score>0
 out=dict(dimension=d,constraints=len(rows),strict_root_queries=q,positive_residues=H)
print(json.dumps(out,indent=2))
