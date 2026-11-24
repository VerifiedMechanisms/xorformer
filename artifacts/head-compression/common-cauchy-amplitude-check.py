#!/usr/bin/env python3
"""Exact finite common-amplitude Cauchy audit, not an asymptotic theorem.

For each relative coefficient-sign assignment, enumerate every independent
active set of the normalized strict sign inequalities.  This is complete,
including degenerate arrangements, since the stacked matrix has full column
rank.  See the companion TeX proof for the elementary active-set argument.
"""
from fractions import Fraction as F
from itertools import combinations,product
def solve_inverse(M):
 n=len(M); R=[list(row)+[F(i==j) for j in range(n)] for i,row in enumerate(M)]
 for j in range(n):
  a=next((i for i in range(j,n) if R[i][j]),None)
  if a is None:return
  R[a],R[j]=R[j],R[a];v=R[j][j];R[j]=[x/v for x in R[j]]
  for i in range(n):
   if i!=j:
    v=R[i][j];R[i]=[x-v*y for x,y in zip(R[i],R[j])]
 return [r[n:] for r in R]
def run(q,power):
 e=F(1,10000);C=[[1/(1-e*(i+h+2))**power for h in range(q)] for i in range(q)];found={};allsg=list(product((-1,1),repeat=q));total=0
 for S in allsg:
  A=C+[[x*s for x,s in zip(row,S)] for row in C]
  for active in combinations(range(2*q),q):
   inv=solve_inverse([A[i] for i in active])
   if inv is None:continue
   for sig in allsg:
    c=[sum(x*s for x,s in zip(row,sig)) for row in inv];y=[sum(x*z for x,z in zip(row,c)) for row in A]
    if all(y):
     word=sum((z>0)<<i for i,z in enumerate(y))
     if word not in found:found[word]={'S':S,'c':[str(v) for v in c]}
    total+=1
 missing=[i for i in range(1<<(2*q)) if i not in found]
 print('q',q,'power',power,'covered',len(found),'missing',missing,'vertices',total,flush=True)
 return {'q':q,'power':power,'epsilon':str(e),'witnesses':found,'missing':missing}
if __name__ == '__main__':
 for power in (1,2):
  result=run(3,power)
  assert len(result['witnesses'])==48
  assert 10 in result['missing']
 # Direct rational checks of the residue dominance used in the theorem.
 total=0
 for poles in ((F(1,100),F(2,100),F(3,100)),
               (F(0),F(1,1000),F(1,10)),
               (F(0),F(99,1000),F(1,10))):
  p1,p2,p3=poles
  for u,v in product((F(1,2),F(1),F(3)),repeat=2):
   Q=lambda p:(u-p)*(v-p)
   r=(Q(p1)/((p2-p1)*(p3-p1)),
      Q(p2)/((p2-p1)*(p3-p2)),
      Q(p3)/((p3-p1)*(p3-p2)))
   for t in (F(1,2),F(1),F(3),F(100)):
    terms=[a/(t-p) for a,p in zip(r,poles)]
    assert terms[1]>terms[0] and terms[1]>terms[2]
    total+=1
 print('Exact residue-dominance checks:',total,flush=True)
