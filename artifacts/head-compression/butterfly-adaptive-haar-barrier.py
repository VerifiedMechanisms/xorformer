#!/usr/bin/env python3
"""High-precision proposals for the biased Haar family, checked exactly.

Usage: heavy python3 butterfly-adaptive-haar-barrier.py 6 1/10 350 OUTPUT
The numerical barrier phase has no authority to declare infeasibility.
A witness is saved only after rational rounding and exact checking of
all original mixed-block inequalities. The separate sample checker
reconstructs biases and verifies every original query. The default
192-bit target uses random.Random(333), solely as a reproducible probe.
Dependencies: python-flint, mpmath. This is finite evidence, not a
universality theorem or a small-parameter continuation certificate.
"""
import importlib.util,json,sys,time,math,random
from pathlib import Path
from fractions import Fraction as F
sys.set_int_max_str_digits(0)
spec=importlib.util.spec_from_file_location('bf',str(Path(__file__).with_name('butterfly-rectangle-decoder-check.py')));bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)
d=int(sys.argv[1]) if len(sys.argv)>1 else 6;eps=F(sys.argv[2]) if len(sys.argv)>2 else F(1,10);H=1<<d;powers=[2**j for j in range(d)];p=[sum((eps**powers[j] for j in range(d) if y&(1<<j)),F(0)) for y in range(H)];sw=bf.switches(d);blocks=list(dict.fromkeys((k,g) for k,s,g in sw));rng=random.Random(333);bits=[rng.randrange(2) for _ in sw];pi=bf.permutation(d,bits);inv=[pi.index(y) for y in range(H)];mixed=[]
for block in blocks:
 bb=[bits[e] for e,(k,s,g) in enumerate(sw) if (k,g)==block]
 if 0 in bb and 1 in bb:mixed.append(block)
N=H+len(mixed);rows=[]
for e,(k,s,g) in enumerate(sw):
 if (k,g) not in mixed:continue
 sign=1-2*bits[e];row=[F(sign*(0 if inv[y]>>(k+1)!=g else 1 if not inv[y]&(1<<k) else -1))/(1-p[s]-p[y]) for y in range(H)]+[F(sign*int(block==(k,g))) for block in mixed];rows.append(row)
from flint import fmpq,fmpq_mat
start=time.time();AA=fmpq_mat([[fmpq(v.numerator,v.denominator) for v in row] for row in rows]);R,rank=AA.transpose().rref();ri=[next(j for j in range(len(rows)) if R[i,j]) for i in range(rank)]
if rank==N:ci=list(range(N))
else:
 RR,rank2=AA.rref();assert rank2==rank;ci=[next(j for j in range(N) if RR[i,j]) for i in range(rank)]
B=fmpq_mat([[AA[i,j] for j in ci] for i in ri]);BI=B.inv();AC=fmpq_mat([[AA[i,j] for j in ci] for i in range(len(rows))]);T=AC*BI
tr=[[F(str(T[i,j])) for j in range(rank)] for i in range(len(rows))];tr=[[a/max(map(abs,row)) for a in row] for row in tr];print('rank',rank,'rows',len(rows),'precondition seconds',time.time()-start,flush=True)
def save(y,method):
 if not all(sum(a*b for a,b in zip(row,y))>0 for row in tr):return False
 Y=fmpq_mat([[fmpq(v.numerator,v.denominator)] for v in y]);Z=BI*Y;c=[F(0)]*N
 for j,col in enumerate(ci):c[col]=F(str(Z[j,0]))
 assert all(sum(a*b for a,b in zip(row,c))>0 for row in rows)
 json.dump(dict(dimension=d,epsilon=str(eps),powers=powers,witnesses=[dict(bits=bits,c=list(map(str,c[:H])))],method=method,basis_rows=ri,basis_columns=ci),open(str(Path(sys.argv[4]) if len(sys.argv)>4 else Path('haar-barrier-witness.json')),'w'),indent=2);print('CERTIFIED',method,'seconds',time.time()-start,flush=True);return True
import mpmath as mp
mp.mp.dps=int(sys.argv[3]) if len(sys.argv)>3 else 250
m=len(tr);n=rank
A=mp.matrix([[mp.mpf(v.numerator)/v.denominator for v in row]+[mp.mpf(1)] for row in tr]);xx=mp.matrix([0]*n+[2]);mu=mp.mpf(1)/m
for it in range(250):
 sl=A*xx-mp.ones(m,1)
 assert min(sl)>0
 grad=mp.matrix([0]*n+[1]);HH=mp.matrix(n+1,n+1)
 for i in range(m):
  u=mu/sl[i];v=u/sl[i]
  for j in range(n+1):
   grad[j]-=u*A[i,j]
   for k in range(j+1):HH[j,k]+=v*A[i,j]*A[i,k]
 for j in range(n+1):
  for k in range(j):HH[k,j]=HH[j,k]
 dx=mp.lu_solve(HH,-grad);decrement=-mp.fdot(grad,dx);ds=A*dx
 upper=min([-mp.mpf('.99')*sl[i]/ds[i] for i in range(m) if ds[i]<0] or [mp.mpf('1e50')])
 def deriv(rate):return dx[n]-mu*sum(ds[i]/(sl[i]+rate*ds[i]) for i in range(m))
 if deriv(upper)<=0:rate=upper
 else:
  lo=mp.mpf(0);hi=min(mp.mpf(1),upper)
  while deriv(hi)<0 and hi<upper:lo=hi;hi=min(2*hi,upper)
  for _ in range(100):
   md=(lo+hi)/2
   if deriv(md)<0:lo=md
   else:hi=md
  rate=(lo+hi)/2
 yy=xx+rate*dx
 xx=yy
 if it%10==0 or xx[n]<0:print('iter',it,'t',mp.nstr(xx[n],8),'step',mp.nstr(rate,4),'decrement',mp.nstr(decrement,4),'seconds',time.time()-start,flush=True)
 if xx[n]<0:
  y=[F(mp.nstr(xx[j],mp.mp.dps-10)) for j in range(n)]
  assert save(y,'high precision barrier proposal, exact rational verification')
  break
 if decrement<mp.mpf('1e-12'):mu/=10
