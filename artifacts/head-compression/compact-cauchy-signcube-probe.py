from fractions import Fraction as F
from math import gcd,comb,log2
from functools import reduce
from random import Random

def lcm(a,b):return a//gcd(a,b)*b

def signs_count(M,etype,seed=0):
 rng=Random(seed)
 eps=F(1,1000*M)
 eta=F(1,1000*M)
 poles=[eps*(2*h+1-M) for h in range(M)]
 ts=[1+eta*(2*j+1-M) for j in range(M)]
 if etype=='equal':a=[F(1) for p in poles]
 elif etype=='zero':a=[1-p for p in poles]
 elif etype=='linear':a=[(1-p)*(1+eps*rng.randint(-3,3)) for p in poles]
 elif etype in ('bary','poly','polyall'):
  roots=[1+eta*(2*j+2-M) for j in range(M-1)] if etype=='polyall' else [1+eta*rng.randint(-M,M) for j in range(M-1)]
  a=[]
  for h,p in enumerate(poles):
   w=F(1)
   for k,q in enumerate(poles):
    if k!=h:w/=p-q
   if etype!='bary':
    for z in roots:w*=p-z
   a.append(w)
 else:raise Exception(etype)
 rows=[]
 for t in ts:
  rr=[v/(t-p) for v,p in zip(a,poles)];den=reduce(lcm,(x.denominator for x in rr),1)
  rows.append([int(x*den) for x in rr])
 cols=list(zip(*rows));cur=[sum(r) for r in rows];prev=0;patterns=set();strict=0
 for k in range(2**M):
  gray=k^(k>>1)
  if k:
   bit=(gray^prev).bit_length()-1
   fac=-2 if(gray>>bit)&1 else 2
   cur=[v+fac*w for v,w in zip(cur,cols[bit])]
  if all(cur):
   pattern=sum((v>0)<<j for j,v in enumerate(cur));patterns.add(pattern);strict+=1
  prev=gray
 return len(patterns),strict
for M in (4,6,8,10,12,14,16):
 for typ in ('equal','zero','linear','bary','poly','polyall'):
  ans=signs_count(M,typ)
  print(M,typ,*ans,'bits',round(log2(ans[0]),3),flush=True)
