import numpy as np, random, time, json
from pathlib import Path
P=1000003
rng=random.Random(260623)
start=time.monotonic();best={};seen=set()
points=list(__import__('itertools').product(range(1,6),repeat=2))
# Moment rows for the three nonzero Boolean directions.
def mat(k):
 return [[pow(a*x+b*y,j,P) for a,b in points] for x,y in ((1,0),(0,1),(1,1)) for j in range(k+1)]
def basis_circuits(M):
 order=list(range(len(points)));rng.shuffle(order)
 piv={}
 for idx in order:
  v=[row[idx] for row in M];comb={idx:1}
  for j,(u,c) in sorted(piv.items()):
   if not v[j]:continue
   a=v[j];v=[(x-a*y)%P for x,y in zip(v,u)]
   for h,b in c.items():comb[h]=(comb.get(h,0)-a*b)%P
  comb={h:a for h,a in comb.items() if a}
  if any(v):
   j=next(i for i,a in enumerate(v) if a);iv=pow(v[j],-1,P)
   piv[j]=([a*iv%P for a in v],{h:a*iv%P for h,a in comb.items()})
  else:yield comb
Mats={k:mat(k) for k in range(2,9)}
trial=0
while time.monotonic()-start<180:
 k=rng.randrange(2,9);trial+=1
 for c in basis_circuits(Mats[k]):
  H=len(c)
  if H>=2*k+2:continue
  nxt=mat(k+1)
  if all(sum(row[h]*a for h,a in c.items())%P==0 for row in nxt):continue
  counts=[]
  for x,y in ((1,0),(0,1),(1,1)):
   agg={}
   for h,a in c.items():
    p=points[h][0]*x+points[h][1]*y;agg[p]=(agg.get(p,0)+a)%P
   counts.append(sum(a!=0 for a in agg.values()))
  if 0 in counts or len(set(counts))==1:continue
  key=(k,H,tuple(counts))
  if key in seen:continue
  seen.add(key);data={'k':k,'H':H,'projection_counts_mod_prime':counts,'points':[points[h] for h in c],'residues_mod_prime':list(c.values()),'prime':P,'trial':trial,'elapsed':time.monotonic()-start}
  print(json.dumps(data),flush=True)
print(json.dumps({'finished':True,'trials':trial,'elapsed':time.monotonic()-start}),flush=True)
