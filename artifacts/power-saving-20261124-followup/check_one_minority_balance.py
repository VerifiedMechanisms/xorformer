#!/usr/bin/env python3
"""Exact standard-library verification of a one-minority basis balance certificate."""
import json
from fractions import Fraction
from pathlib import Path
p=Path(__file__).with_name('one-minority-balance-exact.json')
d=json.loads(p.read_text()); n=d['n']; N=2**n
z=lambda u:[1]+[(u>>(n-1-i))&1 for i in range(n)]
dot=lambda a,b:sum(x*y for x,y in zip(a,b))
F=lambda u:dot(d['w'],z(u))
Z=[z(u) for u in d['basis']]
inv=[[Fraction(a) for a in row] for row in d['basis_inverse']]
assert all(dot(inv[i],[row[j] for row in Z])==int(i==j) for i in range(n+1) for j in range(n+1))
assert [F(u) for u in d['basis']]==[0]*n+[2]
for key in ['positive_b','boundary_optimum_b']:
 b=d[key];B=lambda u:dot(b,z(u));A=lambda u:B(u)-B(d['q'])*F(u)
 assert all((1 if F(u)<=0 else -1)*A(u)>=B(u) for u in range(N))
 assert all(x>0 for x in b) if key=='positive_b' else all(x>=0 for x in b)
 assert all(A(u)==(1 if j<n else -1)*B(u) for j,u in enumerate(d['basis']))
assert sum(d['boundary_optimum_b'])==22*d['boundary_optimum_b'][0]
assert all(F(u)==1 for u in d['dual_rows'])
C=lambda u:[F(u)*z(d['q'])[i]-2*z(u)[i] for i in range(n+1)]
v=[sum(l*C(u)[i] for l,u in zip(d['dual_weights'],d['dual_rows']))+d['dual_nonnegative'].get(str(i),0) for i in range(n+1)]
assert v==[-21]+[1]*n
print(json.dumps({'status':'all exact checks passed','cube_vertices':N,'basis_size':n+1,'positive_contacts':n,'negative_contacts':1,'balance_supremum':'1/22','arithmetic':'Python integers and fractions only'},indent=2))
