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
report = {
    'status': 'exact certificate passed; written proof covers all 0<t<=1/2',
    'symbolic_annihilator_identities': M.cols,
    'integer_score_values_checked': len(values),
    'original_minimum_absolute_cleared_score': min(abs(v) for v in expected),
    'sample_dual_sign_checks': sample_checks,
    'scope': 'prescribed radial denominator path only; not unrestricted head complexity',
}
Path(__file__).with_suffix('.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
