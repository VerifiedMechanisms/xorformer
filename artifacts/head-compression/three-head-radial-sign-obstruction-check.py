#!/usr/bin/env python3
"""Exact universal-parameter dual certificate for a prescribed H3 path."""
from itertools import product
from pathlib import Path
import json
import sympy as s

t = s.symbols('t')
points = list(product((0, 1), repeat=4))
a = (3*t+5)*(3*t*t-16*t-16)/6
b = (3*t+2)*(3*t+5)*(5*t+4)/3
c = -2*t*(3*t+5)*(9*t+8)/9
d = -2*(3*t+5)*(9*t**3+15*t*t-12*t-16)/(3*(2*t+3))
e = (3*t+5)*(6*t*t+t-4)/3
f = -2*(3*t+2)*(3*t+5)*(3*t*t+12*t+8)/(3*(t+3))
g = 2*(t+1)*(3*t+2)*(3*t+5)/3
h = -2*t*(t+1)*(3*t+4)
lam = s.Matrix([0, a, b, c, a, d, 0, e, b, 0, f, g, c, e, g, h])
rows = []
for x in points:
    B = 1+sum(x)
    D, E = x[0]+2*x[1], x[2]+2*x[3]
    rows.append([v*p for p in ((B+t*D)*(B+t*E), B*(B+t*E), B*(B+t*D))
                 for v in (1, *x)])
M = s.Matrix(rows)
assert all(s.factor(v) == 0 for v in lam.T*M)
coefficients = s.Matrix([
    -151022, -108764, 268636, 21418, 8272,
    114799, 119774, -297673, -21143, 0,
    54912, 49152, -81584, 0, 0,
])
values = list(M.subs(t, 1)*coefficients)
expected = [18689, -3960, 3960, -3960, -3960, 3960, -67644, -165836,
            3960, -262917, -3960, 3960, -3960, -165836, 3960, -3960]
assert values == expected
sigma = [s.sign(v) for v in values]
assert all(sigma)
sample_checks = 0
for tau in (s.Rational(1, 2), s.Rational(1, 3), s.Rational(1, 100)):
    weights = list(lam.subs(t, tau))
    assert any(weights)
    assert all(w == 0 or s.sign(w) == sign for w, sign in zip(weights, sigma))
    sample_checks += 1
# Exact polynomial upper bounds used in the written interval proof.
assert s.Rational(3, 4)-16 < 0
assert s.Rational(9, 8)+s.Rational(15, 4)-16 < 0
assert s.Rational(6, 4)+s.Rational(1, 2)-4 == -2

# Independent symbolic audit of the alternative balanced collision.
eps, lc, mc, kc, uc, vc, wc, cc = s.symbols('eps l m k u v w c')
dirs = [kc, kc+lc, kc+mc]
nums = [cc*(lc-mc)+eps*(uc+vc)+eps**2*wc,
        cc*mc-eps*uc, -cc*lc-eps*vc]
cleared = sum(nums[i]*s.prod(1+eps*dirs[j] for j in range(3) if i != j)
              for i in range(3))
pc = cc*lc*mc*(lc-mc)+uc*lc+vc*mc+wc
rc = uc*lc*(kc+mc)+vc*mc*(kc+lc)+wc*(2*kc+lc+mc)
sc = wc*(kc+lc)*(kc+mc)
assert s.expand(cleared-eps**2*(pc+eps*rc+eps**2*sc)) == 0
vectors = [
    [2, 0, 3, 1, -2], [-2, -2, -2, -2, 2], [4, 3, 4, 3, 3],
    [0, s.Rational(34, 3), 0, 0, s.Rational(26, 3)],
    [0, s.Rational(25, 2), s.Rational(131, 6), s.Rational(11, 6), -s.Rational(23, 2)],
    [-s.Rational(13, 3), s.Rational(50, 3), s.Rational(4, 3),
     -s.Rational(46, 3), -s.Rational(34, 3)],
]
alternate_values = []
error_bound = 0
for x, sign in zip(points, sigma):
    vals = [v[0]+sum(a*b for a, b in zip(v[1:], x)) for v in vectors]
    sub = dict(zip((lc, mc, kc, uc, vc, wc), vals))
    sub[cc] = -s.Rational(1, 3)
    pv, rv, sv = [z.subs(sub) for z in (pc, rc, sc)]
    alternate_values.append(pv)
    assert sign*pv >= 1
    error_bound = max(error_bound, abs(rv)+abs(sv))
    tau = s.Rational(1, 14000)
    assert sign*(pv+tau*rv+tau*tau*sv) > s.Rational(1, 2)
assert error_bound == 6700
assert all(z > 0 for z in vectors[2])
assert all(a+b > 0 for a, b in zip(vectors[2], vectors[0]))
assert all(a+b > 0 for a, b in zip(vectors[2], vectors[1]))
report = {
    'status': 'exact certificate passed; written proof covers all 0<t<=1/2',
    'symbolic_annihilator_identities': M.cols,
    'integer_score_values_checked': len(values),
    'original_minimum_absolute_cleared_score': min(abs(v) for v in expected),
    'sample_dual_sign_checks': sample_checks,
    'alternative_three_head_collision_identity': 'symbolically verified',
    'alternative_cube_signs_checked': len(alternate_values),
    'alternative_error_coefficient_bound': int(error_bound),
    'alternative_admissible_interval': '0<epsilon<=1/14000',
    'scope': 'prescribed radial denominator path only; not unrestricted head complexity',
}
Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
