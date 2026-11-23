#!/usr/bin/env python3
"""Exact symbolic certificate of a variable-pole permutation transition.

This checks an oriented-volume sign change, not shattering and not the
requested asymptotic compiler.  Run with: heavy python3 <this file>.
"""
import sympy as S

x, c = S.symbols("x c")
permutations = [
    (0, 1, 2, 3),
    (0, 2, 3, 1),
    (1, 3, 2, 0),
    (3, 0, 1, 2),
]


def cleared_volume(tokens):
    numerators = [
        S.prod(x - tokens[j] for j in range(4) if j != i)
        for i in range(4)
    ]
    matrix = S.Matrix([
        [numerators[permutations[i][h]] - numerators[permutations[3][h]]
         for h in range(3)]
        for i in range(3)
    ])
    return S.Poly(S.expand(matrix.det()), x)


concrete = cleared_volume([112, 273, 707, 788])
concrete_expected = -5 * (x - 707) * (x - 112) * (
    5275 * x**4 - 6245360632 * x**3 + 8524750604517 * x**2
    - 3261701068819508 * x + 248767066754926160
)
assert S.expand(concrete.as_expr() - concrete_expected) == 0
assert concrete.eval(10000) > 0
assert concrete.eval(100000000) < 0

family = cleared_volume([0, S.Rational(1, 4), c, 1])
leading = -(16*c**2 + 44*c - 51) / 64
next_coefficient = c**3 / 4 + 9*c**2 / 4 - 47*c / 32 - S.Rational(15, 32)
assert S.expand(family.coeff_monomial(x**6) - leading) == 0
assert S.expand(family.coeff_monomial(x**5) - next_coefficient) == 0
c0 = (-11 + 5*S.sqrt(13)) / 8
assert S.simplify(leading.subs(c, c0)) == 0
next_at_c0 = S.Rational(363, 32) - 795*S.sqrt(13)/256
assert S.simplify(next_coefficient.subs(c, c0) - next_at_c0) == 0
# Verify the positive radical comparison by integer arithmetic.
assert 2904**2 > 795**2 * 13
assert (S.Rational(1, 4) < c0) == True
assert (c0 < 1) == True
assert S.diff(leading, c) == -c/2 - S.Rational(11, 16)

# Three increasingly far, entirely rational sign-changing brackets.
# These are illustrative certificates; arbitrary distance follows from
# the leading/next coefficient identities proved above.
for denominator, lower, upper in [
    (10**4, 10, 10**7),
    (10**6, 100, 10**9),
    (10**8, 1000, 10**11),
]:
    c_rational = S.Rational(int(S.floor(c0 * denominator)) + 1, denominator)
    polynomial = S.Poly(family.as_expr().subs(c, c_rational), x)
    assert polynomial.eval(lower) > 0
    assert polynomial.eval(upper) < 0
    print(f"rational c={c_rational}: opposite signs at {lower}, {upper}")

print("Verified two polynomial identities, the far-transition coefficients, and four exact brackets.")
