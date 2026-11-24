#!/usr/bin/env python3
"""Exact rational checks for the fixed origin-contact counterexample and balance."""
import json
from pathlib import Path
from sympy import Matrix, Rational
p=Path('artifacts/power-saving-20261124-followup/origin-contact-basis-n6.json')
o=json.loads(p.read_text()); e=o['exact_counterexample']; n=o['n']
X=Matrix([[1]+[(i>>(n-1-j))&1 for j in range(n)]for i in range(2**n)])
V=X[e['basis'],:]; sig=Matrix.diag(*e['signs']); T=V.inv()*sig*V
f=[1 if v else -1 for v in e['labels']]
assert V.det()!=0 and e['basis'][0]==0
b=Matrix([Rational(v)for v in o['small_integer']['b']]);a=T*b
assert list(a)==[Rational(v)for v in o['small_integer']['a']]
assert all(v>0 for v in b)
assert all(ff*av>=bv for ff,av,bv in zip(f,X*a,X*b))
constant=T[:,0]
assert list(constant)==[Rational(v)for v in e['aconst']]
assert all(abs(v)>=1 for v in X*constant)
assert (X*a)[11]==-4 and (X*b)[11]==4 and (X*constant)[11]==1
boundary=Matrix([1,1,0,0,0,0,0]); boundary_a=T*boundary
assert all(ff*av>=bv for ff,av,bv in zip(f,X*boundary_a,X*boundary))
assert list(-X[11,:]*T-X[11,:])==[-2,2,-2,0,0,0,-2]
assert boundary[0]/sum(boundary)==Rational(1,2)
out={'status':'all checks exact rational arithmetic','determinant':str(V.det()),
     'contact_rows':7,'vertices':64,'small_positive_denominator':list(map(str,b)),
     'boundary_denominator':list(map(str,boundary)),
     'boundary_numerator':list(map(str,boundary_a)),
     'vertex_11_negative_gap_coefficients':[-2,2,-2,0,0,0,-2],
     'intercept_fraction_supremum':'1/2'}
Path('artifacts/power-saving-20261124-followup/origin-contact-exact-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
