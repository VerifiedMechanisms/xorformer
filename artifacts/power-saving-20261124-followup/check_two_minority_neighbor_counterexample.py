#!/usr/bin/env python3
"""Recover and check the neighbor-cell example with exact fractions."""
import itertools,json,math
from fractions import Fraction as F
from pathlib import Path
root=Path(__file__).parent
src=json.loads((root/'two-minority-neighbor-variable-cells-n8.json').read_text());r=src['records'][0];n=src['n'];d=n+1
X=[[F(1),*map(F,bits)] for bits in itertools.product([0,1],repeat=n)]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def mul(A,B):return [[dot(row,col) for col in zip(*B)] for row in A]
def inverse(A):
 m=len(A);V=[list(row)+[F(i==j) for j in range(m)] for i,row in enumerate(A)]
 for i in range(m):
  j=next(j for j in range(i,m)if V[j][i]);V[i],V[j]=V[j],V[i];a=V[i][i];V[i]=[x/a for x in V[i]]
  for j in range(m):
   if j!=i:
    a=V[j][i];V[j]=[x-a*y for x,y in zip(V[j],V[i])]
 return [row[m:] for row in V]
Z=[X[i] for i in r['basis']];Zi=inverse(Z);g=[-1 if j in r['negative_positions'] else 1 for j in range(d)];T=mul(Zi,[[sg*x for x in row]for sg,row in zip(g,Z)])
labels=[];bs=[];aas=[];sigs=[];ratios=[];sign=lambda x:int(x>0)-int(x<0)
for w in r['witnesses']:
 b=[F(float(x)).limit_denominator(1000000) for x in w['denominator']];den=math.lcm(*(x.denominator for x in b));b=[x*den for x in b];a=[dot(row,b) for row in T]
 den=math.lcm(*(x.denominator for x in a));b=[x*den for x in b];a=[x*den for x in a]
 assert all(x>0 for x in b)
 B=[dot(x,b)for x in X];A=[dot(x,a)for x in X]
 assert all(abs(v)>=u>0 for v,u in zip(A,B))
 assert [A[j]/B[j]for j in r['basis']]==list(map(F,g))
 q1,q2=[r['basis'][j]for j in r['negative_positions']];rr=B[q1]/B[q2];c=[(u-v)/(2*B[q2])for u,v in zip(b,a)]
 sig=[sign(x)for x in c]+[sign(x+rr)for x in c]+[sign(x+1)for x in c]+[sign(x-rr)for x in c]+[sign(x-1)for x in c]
 labels.append([sign(x)for x in A]);bs.append(b);aas.append(a);sigs.append(sig);ratios.append(rr)
assert sigs[0]==sigs[1]
diff=[i for i in range(2**n)if labels[0][i]!=labels[1][i]];assert diff
out={'status':'all exact rational checks passed','n':n,'basis':r['basis'],'basis_signs':g,'inverse_basis':Zi,'matrixT':T,'denominators':bs,'numerators':aas,'ratios':ratios,'comparison_signature':sigs[0],'disagreement':diff}
def enc(x):
 if isinstance(x,F):return int(x)if x.denominator==1 else str(x)
 raise TypeError(type(x))
(root/'two-minority-neighbor-exact.json').write_text(json.dumps(out,indent=2,default=enc)+'\n')
print(json.dumps({'status':out['status'],'cube_rows':2**n,'basis':out['basis'],'ratios':ratios,'disagreement':diff,'denominators':bs,'numerators':aas},indent=2,default=enc))
