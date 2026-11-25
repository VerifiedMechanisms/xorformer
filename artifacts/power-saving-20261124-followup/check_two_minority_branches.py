#!/usr/bin/env python3
"""Check the saved seven-bit counterexample using Python integers only."""
import json,itertools
from pathlib import Path
p=Path(__file__).with_name('two-minority-branches-exact.json');r=json.loads(p.read_text());n=r['n'];d=n+1
X=[[1,*bits]for bits in itertools.product([0,1],repeat=n)]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def mul(A,B):return [[dot(row,col)for col in zip(*B)]for row in A]
Z=[X[i]for i in r['basis']];T=r['matrixT'];I=[[int(i==j)for j in range(d)]for i in range(d)]
assert mul(r['inverse_basis'],Z)==I
assert mul(Z,T)==[[g*x for x in row]for g,row in zip(r['basis_signs'],Z)]
assert sum(g==-1 for g in r['basis_signs'])==2
labels=[];coefficient_signs=[]
sign=lambda x:(x>0)-(x<0)
for b,a in zip(r['denominators'],r['numerators']):
 assert all(t>0 for t in b)
 assert [dot(row,b)for row in T]==a
 f=[sign(dot(row,a))for row in X];labels.append(f)
 C=[[f[i]*z-t for z,t in zip(row,X[i])]for i,row in enumerate(mul(X,T))]
 structural=[i for i,row in enumerate(C)if not any(row)]
 assert structural==r['structural_rows']
 residual=[dot(row,b)for row in C]
 assert min(residual)>=0
 assert min(residual[i]for i in range(2**n)if i not in structural)>=2
 assert [f[i]for i in r['basis']]==r['basis_signs']
 coefficient_signs.append([sign(x-y)for x,y in zip(b,a)])
assert coefficient_signs[0]==coefficient_signs[1]
assert [i for i in range(2**n)if labels[0][i]!=labels[1][i]]==r['disagreement']
print(json.dumps({'status':'all exact integer checks passed','cube_rows':2**n,'negative_contacts':2,'disagreement':r['disagreement'],'common_difference_coefficient_signs':coefficient_signs[0]},indent=2))
