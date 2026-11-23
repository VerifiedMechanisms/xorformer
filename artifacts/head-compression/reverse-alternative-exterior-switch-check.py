#!/usr/bin/env python3
"""Exact determinant and cube-margin checks for the exterior Cauchy switch."""
import sympy as sp

T, t, A = sp.symbols("T t A")
poles = (1, 2, 3, A)
permutations = ((0, 1, 2, 3), (0, 2, 1, 3),
                (1, 0, 3, 2), (2, 1, 3, 0))
mat = sp.Matrix([[1] + [1 / (t - poles[p[h]]) for h in range(3)]
                 for p in permutations])
expected = -((A - 5) * t**2 + 12 * t - 5 * A - 3) / (
    (A - t) * (t - 3)**3 * (t - 2)**2 * (t - 1)**2)
assert sp.cancel(mat.det() - expected) == 0
chosen_A = (5 * T**2 - 12 * T + 3) / (T**2 - 5)
tau = (7 * T - 15) / (3 * T - 7)
assert sp.cancel(((A - 5) * t**2 + 12 * t - 5 * A - 3).subs(A, chosen_A)
                 - (chosen_A - 5) * (t - T) * (t - tau)) == 0
assert sp.cancel(chosen_A - 3 - 2 * (T - 3)**2 / (T**2 - 5)) == 0
assert sp.cancel(5 - chosen_A - 4 * (3 * T - 7) / (T**2 - 5)) == 0
assert sp.cancel(3 - tau - 2 * (T - 3) / (3 * T - 7)) == 0
for center in (10, 100, 1000, 1000000):
    token = chosen_A.subs(T, center)
    assert 3 < token < 5
    assert expected.subs({A: token, t: center - 1}) > 0
    assert expected.subs({A: token, t: center}) == 0
    assert expected.subs({A: token, t: center + 1}) < 0
for rows, columns in ((2, 1), (4, 16), (100, 1000)):
    center = 3 * rows + 5 * columns + 10
    intercept = center + 2
    row_poles = [center - 1, center + 1] + [center] * (rows - 2)
    slopes = [intercept - value for value in row_poles]
    assert min(slopes) > 0
    assert sum(slopes) + 5 * columns < intercept
print("PASS: exact determinant, factorization, exterior signs, and cube margins")
