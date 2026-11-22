"""Exact audit of an order-preserving change of two-head feasibility."""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json

p = Path(__file__).with_name('denominator-order-certificate.json')
d = json.loads(p.read_text())
cube = list(product([0, 1], repeat=4))

def affine(coeff, x):
    return coeff[0] + sum(a * b for a, b in zip(coeff[1:], x))

def row(x, left):
    a = affine(d['A_coefficients'], x)
    b = affine(d['B_left_coefficients'] if left else d['B_right_coefficients'], x)
    return [a * b] + [v * b for v in x] + [v * a for v in x]

assert all(c > 0 for name in ['A_coefficients', 'B_left_coefficients', 'B_right_coefficients'] for c in d[name])
left = [affine(d['B_left_coefficients'], x) for x in cube]
right = [affine(d['B_right_coefficients'], x) for x in cube]
a = [affine(d['A_coefficients'], x) for x in cube]
assert len(set(left)) == len(set(right)) == len(set(a)) == 16
assert all((left[i] < left[j]) == (right[i] < right[j]) for i in range(16) for j in range(16))
assert left == d['all_left_B_values'] and right == d['all_right_B_values'] and a == d['all_A_values']
assert len(set(d['rows'])) == 10
ml = [row(cube[j], True) for j in d['rows']]
mr = [row(cube[j], False) for j in d['rows']]
assert ml == d['left_matrix'] and mr == d['right_matrix']
c = d['left_kernel']
assert all(c[i] * d['labels'][i] > 0 for i in range(10))
assert all(sum(c[i] * ml[i][j] for i in range(10)) == 0 for j in range(9))
u = d['right_coefficients']
z = [sum(a * b for a, b in zip(row(x, False), u)) for x in cube]
assert z == d['all_right_cleared_scores'] and all(z)
assert [z[j] for j in d['rows']] == d['right_cleared_scores']
assert all(c[i] * z[d['rows'][i]] > 0 for i in range(10))
for j, x in enumerate(cube):
    direct = Fraction(u[0]) + Fraction(sum(u[i + 1] * x[i] for i in range(4)), a[j]) + Fraction(sum(u[i + 5] * x[i] for i in range(4)), right[j])
    assert direct == Fraction(z[j], a[j] * right[j])
print('PASS: positive coefficients; strict identical denominator orders; exact annihilator; strict right witness; all 16 score identities')
