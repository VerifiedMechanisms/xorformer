#!/usr/bin/env python3
"""Exact tests for two-head-sign-coalescence.tex; no floating-point tests."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import random
import sympy as sp


def ev(coef, x):
    return coef[0] + sum((c * z for c, z in zip(coef[1:], x)), Q(0))


rng = random.Random(20261124)
point_checks = 0
orientation_checks = 0
for n in range(1, 7):
    for first_sign in (-1, 1):
        for second_sign in (-1, 0, 1):
            slopes1 = [Q(first_sign * rng.randrange(1, 5)) for _ in range(n)]
            slopes2 = [Q(second_sign * rng.randrange(1, 5)) for _ in range(n)]
            b1 = [Q(1) + sum(abs(c) for c in slopes1), *slopes1]
            b2 = [Q(1) + sum(abs(c) for c in slopes2), *slopes2]
            a1 = [Q(rng.randrange(-5, 6)) for _ in range(n + 1)]
            a2 = [Q(rng.randrange(-5, 6)) for _ in range(n + 1)]
            for t in (Q(1, 16), Q(1, 32), Q(1, 128)):
                c2 = [(1-t)*u+t*v for u, v in zip(b1, b2)]
                n1 = [u/t for u in a1]
                n2 = [u+v-u/t for u, v in zip(a1, a2)]
                assert all(first_sign*c > 0 for c in c2[1:])
                orientation_checks += 1
                for x in product((0, 1), repeat=n):
                    assert ev(b1, x) > 0 and ev(b2, x) > 0 and ev(c2, x) > 0
                    old = ev(a1, x)/ev(b1, x) + ev(a2, x)/ev(b2, x)
                    new = ev(n1, x)/ev(b1, x) + ev(n2, x)/ev(c2, x)
                    assert new == old * ev(b2, x)/ev(c2, x)
                    assert (new > 0) == (old > 0)
                    assert (new == 0) == (old == 0)
                    point_checks += 1

t = sp.symbols('t')
points = list(product((0, 1), repeat=3))
lam = sp.Matrix([
    -(t+1)*(t+4), (t+2)*(t+4)/4, (t+4)/2, -(t+4)/3,
    (t+4)/2, -(t+4)/3, -(t+4)/(t+3), 1,
])
rows = []
target = []
signed_target = []
for x, y, z in points:
    b = 1+x+y+z
    c2, c3 = b+t*x, b+t*y
    rows.append([v*p for p in (c2*c3, b*c3, b*c2) for v in (1, x, y, z)])
    target.append((b+x)*(b+y))
    signed_target.append((2*x-1)*(b+x)*(b+y))
matrix = sp.Matrix(rows)
annihilation = lam.T * matrix
assert all(sp.factor(v) == 0 for v in annihilation)
for values in (target, signed_target):
    assert sp.factor((lam.T*sp.Matrix(values))[0]) == -(t-1)**2/(t+3)
half = matrix.subs(t, sp.Rational(1, 2))
rank = half.rank()
augmented_rank = half.row_join(sp.Matrix(target)).rank()
assert (rank, augmented_rank) == (7, 8)

report = {
    'status': 'exact checks passed; universal claims have written proofs, not Lean formalization',
    'two_head_cube_point_checks': point_checks,
    'strict_common_orientation_checks': orientation_checks,
    'symbolic_annihilator_identities': len(annihilation),
    'symbolic_target_separations': 2,
    'three_head_rank_at_half': rank,
    'three_head_augmented_rank_at_half': augmented_rank,
    'scope': 'H3 obstruction preserves cleared cube values only, not signs',
}
path = Path(__file__).with_suffix('.json')
path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
