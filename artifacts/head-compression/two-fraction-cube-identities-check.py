#!/usr/bin/env python3
"""Exact checks of the examples and homogenized rank formula."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import sympy as s

x, y, z = s.symbols('x y z')
B = (2885*x + 5*y + 6*z + 184) / s.Integer(5100)
L = 1195*x + 5*y + 76
M = 1393*x - y + 92
K = 102*(2885*x + 5*y - 6*z + 190)
D, A, C = B + L, -M/10, -M/10 - K
cross = s.expand(A*D - C*B)
assert s.expand(cross - (x*(x-1) + y*(y-1) - s.Rational(18,25)*z*(z-1))) == 0
for den in (B, D):
    poly = s.Poly(den, x, y, z)
    assert poly.coeff_monomial(1) > 0
    assert all(poly.coeff_monomial(v) > 0 for v in (x,y,z))
for point in product((0,1), repeat=3):
    sub = dict(zip((x,y,z),point))
    assert cross.subs(sub) == 0
    assert B.subs(sub) > 0 and D.subs(sub) > 0
    assert (A/B-C/D).subs(sub) == 0

n = 5
for point in product((0,1), repeat=n):
    base = Q(10 + 2*sum(point))
    aa = Q(point[0]-1)
    dd = base + point[0]
    assert aa/base == aa/dd
    aa = Q(point[0]+point[1]-1)
    dd = base + point[0]-point[1]
    assert aa/base == aa/dd

ranks = []
for coeffs in ([1], [1,-1], [1,2], [1,2,-3], [1,1,-s.Rational(18,25)], [1,2,-1,-2]):
    k = len(coeffs)
    mat = s.zeros(k+1)
    for i, c in enumerate(coeffs,1):
        mat[i,i] = c
        mat[0,i] = mat[i,0] = -s.Rational(c)/2
    rank = mat.rank()
    expected = k if sum(coeffs) == 0 else k+1
    assert rank == expected
    ranks.append({"coefficients": list(map(str,coeffs)), "rank": rank})

out = {"status": "all exact checks passed", "three_variable_vertex_checks": 8,
       "five_variable_vertex_checks": 64, "rank_checks": ranks,
       "scope": "written classification and exact examples, not Lean or asymptotic lower bound"}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({"status":out["status"],"vertex_checks":72,"rank_checks":len(ranks)}))
