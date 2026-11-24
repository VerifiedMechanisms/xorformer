"""Finite numerical screen only: low-rank reciprocal matrices vs Cauchy banks.
Run via heavy. A failed optimizer is not an impossibility certificate.
"""
import argparse,json,numpy as np
from scipy.optimize import least_squares

def main():
 p=argparse.ArgumentParser();p.add_argument('--rows',type=int,default=12);p.add_argument('--cols',type=int,default=8);p.add_argument('--heads',type=int,default=2);p.add_argument('--starts',type=int,default=8);p.add_argument('--seed',type=int,default=1);p.add_argument('--evaluations',type=int,default=3000);p.add_argument('--column-scale',action='store_true');args=p.parse_args()
 rng=np.random.default_rng(args.seed);r,s,h=args.rows,args.cols,args.heads
 U=rng.uniform(-.3,.3,(r,2));V=rng.uniform(-.3,.3,(s,2));Y=1/(1+U@V.T)
 # Positive compact denominators d_i+t_j, each term independent. Signed residues.
 def unpack(z):
  k=0; A=z[k:k+h*r].reshape(h,r);k+=h*r
  D=np.exp(z[k:k+h*r].reshape(h,r));k+=h*r
  T=np.exp(z[k:k+h*s].reshape(h,s));k+=h*s
  if args.column_scale:B=z[k:k+h*s].reshape(h,s)
  else:B=np.ones((h,s))
  return A,D,T,B
 def fun(z):
  A,D,T,B=unpack(z);return (np.sum(A[:,:,None]*B[:,None,:]/(D[:,:,None]+T[:,None,:]),axis=0)-Y).ravel()
 best=None
 for start in range(args.starts):
  A=rng.normal(2/h,.1,(h,r));D=rng.normal(0,.2,(h,r));T=rng.normal(0,.2,(h,s));zs=[A.ravel(),D.ravel(),T.ravel()]
  if args.column_scale:zs.append(rng.normal(1,.1,(h,s)).ravel())
  z=np.concatenate(zs)
  fit=least_squares(fun,z,max_nfev=args.evaluations,ftol=1e-13,xtol=1e-13,gtol=1e-13,method='trf')
  residual=float(np.max(np.abs(fun(fit.x))));l2=float(np.linalg.norm(fun(fit.x)))
  rec={'start':start,'linf':residual,'l2':l2,'nfev':fit.nfev,'status':int(fit.status)}
  print(json.dumps(rec),flush=True)
  if best is None or residual<best['linf']:best=rec
  if residual<1e-10:break
 print(json.dumps({'args':vars(args),'best':best,'status':'numerical_only'}),flush=True)
if __name__=='__main__':main()
