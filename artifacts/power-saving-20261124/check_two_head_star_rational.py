"""Exact Fraction audit of a two-head 5-by-32 strict sign table.

The JSON was discovered with Z3 QF_NRA, but this checker only performs
rational arithmetic. It checks the finite certificate, not a universal
statement about head lower bounds or degenerating representations.
"""
from fractions import Fraction as F
from pathlib import Path
import json
p=Path(__file__).with_name('two_head_star_rational.json')
data=json.loads(p.read_text())
u,z,r,t=([F(x) for x in data[k]] for k in ('u','z','r','t'))
witnesses={int(k):[F(x) for x in v] for k,v in data['witnesses'].items()}
assert set(witnesses)==set(range(32))
for code,(v,q,s,w) in witnesses.items():
    assert min(u)+v>0 and min(z)+q>0
    for i in range(5):
        score=(r[i]+s)/(u[i]+v)+(t[i]+w)/(z[i]+q)
        assert score != 0
        assert (score>0)==bool(code & (1<<i))
# Compile all 32 columns jointly to two positive affine denominators
# on 37 Boolean coordinates, queried at e_i+e_(5+code).
vmin=min(row[0] for row in witnesses.values())
qmin=min(row[1] for row in witnesses.values())
eps=min(min(u)+vmin,min(z)+qmin)/4
constants=[min(u)+vmin-2*eps,min(z)+qmin-2*eps]
slopes1=[a-min(u)+eps for a in u]+[witnesses[j][0]-vmin+eps for j in range(32)]
slopes2=[a-min(z)+eps for a in z]+[witnesses[j][1]-qmin+eps for j in range(32)]
assert min(constants+slopes1+slopes2)>0
for code,(v,q,s,w) in witnesses.items():
    for i in range(5):
        assert constants[0]+slopes1[i]+slopes1[5+code]==u[i]+v
        assert constants[1]+slopes2[i]+slopes2[5+code]==z[i]+q
print(json.dumps({'all_160_signs_verified':True,'cube_dimension':37,
                  'strictly_positive_denominator_constants':list(map(str,constants)),
                  'smallest_denominator_slope':str(min(slopes1+slopes2)),
                  'solver_not_used_by_checker':True},indent=2))
