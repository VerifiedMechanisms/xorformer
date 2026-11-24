#!/usr/bin/env python3
"""Extract and verify exact rational LP certificates from exploratory records.
All final matrix equalities and inequalities use sympy rationals.
"""
import argparse, json
from pathlib import Path
from fractions import Fraction
import numpy as np
import sympy as s
from scipy.optimize import linprog
p=argparse.ArgumentParser(); p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
data=json.loads(args.input.read_text());n=data['n'];d=n+1;N=2**n
X=s.Matrix([[1]+[(x>>(n-1-i))&1 for i in range(n)] for x in range(N)])
def rational(v):return s.Rational(Fraction(float(v)).limit_denominator(10**9))
results=[]
for rec in data['records'][-3:]:
 ids=rec['basis'];g=[int(v) for v in rec['basis_labels']];f=[int(v) for v in rec['full_labels']]
 Z=X[ids,:];T=Z.inv()*s.diag(*g)*Z
 C=s.diag(*f)*X*T-X
 Cf=np.array(C,float)
 fit=linprog(np.r_[-1.,np.zeros(d-1)],A_ub=-Cf,b_ub=np.zeros(N),A_eq=np.ones((1,d)),b_eq=[1.],bounds=[(0,None)]*d,method='highs')
 assert fit.success
 lam=rational(-fit.fun);b=s.Matrix([rational(v) for v in fit.x]);inds=np.flatnonzero(np.abs(fit.ineqlin.marginals)>1e-9)
 y=s.Matrix([rational(-fit.ineqlin.marginals[i]) for i in inds])
 slack=lam*s.ones(d,1)-C[list(inds),:].T*y-s.eye(d)[:,0]
 primal_ok=all(v>=0 for v in b) and sum(b)==1 and all(v>=0 for v in C*b) and b[0]==lam
 dual_ok=all(v>=0 for v in y) and all(v>=0 for v in slack)
 # A separate positive coefficient witness in this same full-label region.
 A=np.vstack([np.column_stack([-Cf,np.zeros(N)]),np.column_stack([-np.eye(d),np.ones(d)])])
 pos=linprog(np.r_[np.zeros(d),-1.],A_ub=A,b_ub=np.zeros(N+d),A_eq=np.array([[1.]*d+[0.]]),b_eq=[1.],bounds=[(0,None)]*(d+1),method='highs')
 bp=s.Matrix([rational(v) for v in pos.x[:d]]) if pos.success else s.zeros(d,1)
 positive_ok=all(v>0 for v in bp) and sum(bp)==1 and all(v>=0 for v in C*bp)
 result={'n':n,'basis':ids,'basis_labels':g,'maximum_b0':str(lam),'balanced_b':[str(v) for v in b],
 'dual_rows':[int(i) for i in inds],'dual_weights':[str(v) for v in y],'dual_slack':[str(v) for v in slack],
 'positive_b':[str(v) for v in bp],'positive_a':[str(v) for v in T*bp],
 'primal_exact':bool(primal_ok),'dual_exact':bool(dual_ok),'positive_witness_exact':bool(positive_ok),
 'full_labels':f}
 results.append(result)
 print({k:v for k,v in result.items() if k not in ['full_labels','positive_a']},flush=True)
args.output.write_text(json.dumps({'method':'Exact rational primal, dual, and full-cube witness checks','results':results},indent=2)+'\n')
assert all(r['primal_exact'] and r['dual_exact'] and r['positive_witness_exact'] for r in results)
