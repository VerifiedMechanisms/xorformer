"""High-precision exploratory continuation of the certified small-margin branch.

This computation does not certify continuation intervals or prove an obstruction.
The exact base point, labels, and tangent are independently checked elsewhere.
All returned nonzero-margin points remain numerical candidates only.
"""
import argparse,json,time
from fractions import Fraction
from pathlib import Path
import mpmath as mp
import numpy as np


def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
 p.add_argument('--seconds',type=float,default=5400);p.add_argument('--digits',type=int,default=70)
 a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);mp.mp.dps=a.digits
 root=Path(__file__).parent;data=json.loads((root/'integer-zero-fiber-16.json').read_text())
 dualdata=json.loads((root/'zero-fiber-dual-checks.json').read_text());full=json.loads((root/'fullcube-active-minimum-checks.json').read_text())
 n,h=data['n'],data['heads'];k=n*h;m=2*k
 theta=mp.matrix([mp.mpf(v)/data['numerator_scale'] for row in data['numerator_scaled_slopes'] for v in row]+[mp.mpf(v) for row in data['denominator_slopes'] for v in row])
 sample=data['sample_indices'];bits=[[(v>>i)&1 for i in range(n)] for v in sample]
 y=mp.matrix(dualdata['labels']);eps=mp.mpf('0');step=mp.mpf('1e-14');start=time.monotonic();trial=0
 raw=bytes.fromhex(full['truth_table_hex_little_endian_bits']);all_y=np.array([1 if raw[v//8]>>(v%8)&1 else -1 for v in range(2**n)])
 cube=((np.arange(2**n)[:,None]>>np.arange(n))&1).astype(float);others=np.setdiff1d(np.arange(2**n),sample)
 class Expired(Exception):pass
 def evaluate(t):
  if time.monotonic()-start>a.seconds:raise Expired
  f=mp.matrix(m,1);j=mp.matrix(m,m)
  for r,x in enumerate(bits):
   d=[1+sum(t[k+g*n+i] for i in range(n) if x[i]) for g in range(h)]
   num=[sum(t[g*n+i] for i in range(n) if x[i]) for g in range(h)]
   f[r]=1+sum(num[g]/d[g] for g in range(h))
   for g in range(h):
    for i in range(n):
     if x[i]:j[r,g*n+i]=1/d[g];j[r,k+g*n+i]=-num[g]/d[g]**2
  return f,j
 f,j=evaluate(theta);assert max(abs(v) for v in f)<mp.mpf('1e-60')
 tangent=mp.lu_solve(j,y)
 exact=[Fraction(v) for v in full['tangent_direction']]
 check=max(abs(tangent[i]-mp.mpf(v.numerator)/v.denominator) for i,v in enumerate(exact))
 print(json.dumps({'base_tangent_error':mp.nstr(check,12),'status':'NUMERICAL_BASE_CHECK'}),flush=True)
 with (a.output/'results.jsonl').open('a',buffering=1) as log:
  try:
   while time.monotonic()-start<a.seconds and eps<1 and step>mp.mpf('1e-35'):
    target=min(mp.mpf(1),eps+step);t=theta+(target-eps)*tangent;accepted=False
    for it in range(16):
     if min(t[k:])<=0:break
     f,j=evaluate(t);res=f-target*y;err=max(abs(v) for v in res)
     if err<mp.mpf('1e-45'):accepted=True;break
     delta=mp.lu_solve(j,res);length=mp.mpf(1)
     while length>mp.mpf('1e-8'):
      proposal=t-length*delta
      if min(proposal[k:])>0:
       fv,_=evaluate(proposal)
       if max(abs(v) for v in fv-target*y)<err:
        t=proposal;break
      length/=2
     else:break
    if not accepted:
     step/=2;trial+=1;continue
    theta=t;eps=target;f,j=evaluate(theta);tangent=mp.lu_solve(j,y)
    grad=mp.matrix([2*theta[i] if i<k else 0 for i in range(m)])
    lam=mp.lu_solve(j.T,grad);signed=[lam[i]*y[i] for i in range(m)]
    arr=np.array([float(v) for v in theta]);num=cube@arr[:k].reshape(h,n).T;den=1+cube@arr[k:].reshape(h,n).T;score=1+(num/den).sum(axis=1)
    slacks=all_y*score-float(eps);minimum=float(slacks[others].min());worst=int(others[np.argmin(slacks[others])])
    rec={'status':'NUMERICAL_CONTINUATION_ONLY','trial':trial,'epsilon':mp.nstr(eps,30),'step':mp.nstr(step,20),
     'newton_iterations':it,'sample_residual':mp.nstr(max(abs(v) for v in f-eps*y),12),
     'minimum_slope':mp.nstr(min(theta[k:]),20),'minimum_signed_dual':mp.nstr(min(signed),20),
     'negative_dual_count':sum(v<0 for v in signed),'float_unsampled_min_slack':minimum,'worst_vertex':worst,
     'elapsed_seconds':time.monotonic()-start,'main_target_proved':False}
    log.write(json.dumps(rec)+'\n');print(json.dumps(rec),flush=True)
    (a.output/'last-point.json').write_text(json.dumps(dict(rec,theta=[mp.nstr(v,a.digits) for v in theta]),indent=2)+'\n')
    if min(signed)<=0 or minimum < -1e-10:
     print(json.dumps({'status':'BRANCH_DIAGNOSTIC_LOST','no_impossibility_claim':True}),flush=True);break
    step*=mp.mpf('1.3');trial+=1
  except (Expired,ZeroDivisionError,ValueError) as ex:
   print(json.dumps({'status':'CONTINUATION_STOPPED_UNKNOWN','reason':type(ex).__name__}),flush=True)
 print(json.dumps({'status':'FINISHED_UNKNOWN','epsilon':mp.nstr(eps,30),'elapsed_seconds':time.monotonic()-start,'main_target_proved':False}),flush=True)


if __name__=='__main__':main()
