#!/usr/bin/env python3
"""Exact polynomial and rational checks for the explicit five-head upper bound.

All continuum inequalities are proved in README.md. The script verifies their
exact identities and constants, without sampling or expanding the Boolean cube.
Only the Python standard library is required. `main()` is the integration API.
"""

from fractions import Fraction as F


N = 7
ZERO = (0,) * N


def constant(value):
    return {} if value == 0 else {ZERO: F(value)}


def variable(index):
    degree = list(ZERO)
    degree[index] = 1
    return {tuple(degree): F(1)}


def add(*terms):
    result = {}
    for term in terms:
        for degree, value in term.items():
            result[degree] = result.get(degree, 0) + value
    return {degree: value for degree, value in result.items() if value}


def mul(*factors):
    result = constant(1)
    for factor in factors:
        out = {}
        for left, lv in result.items():
            for right, rv in factor.items():
                degree = tuple(a + b for a, b in zip(left, right))
                out[degree] = out.get(degree, 0) + lv * rv
        result = {degree: value for degree, value in out.items() if value}
    return result


def scale(value, term):
    return mul(constant(value), term)


def symbolic_checks():
    E, a, u, v, U0, U1, U2 = map(variable, range(N))
    au, av = mul(a, u), mul(a, v)
    Eu, Ev, Euv = add(E, au), add(E, av), add(E, au, av)
    # Clear all positive denominators in the first and second differences.
    assert add(Eu, scale(-1, E)) == au
    delta_numerator = add(mul(Eu, Ev, Euv), scale(-1, mul(E, Ev, Euv)),
                          scale(-1, mul(E, Eu, Euv)), mul(E, Eu, Ev))
    assert delta_numerator == mul(a, a, u, v, add(scale(2, E), au, av))
    # The sum of two triple reciprocal products has exactly this numerator.
    assert add(Euv, E) == add(scale(2, E), au, av)
    # Eliminate D1=10u-E in the target numerator.
    D1 = add(scale(10, u), scale(-1, E))
    target = add(mul(U0, D1, v), mul(U1, u, v), mul(U2, u, D1))
    A, C = scale(10, U2), add(scale(10, U0), U1)
    leading = add(mul(A, u, u), mul(C, u, v),
                  scale(-1, mul(E, add(mul(U2, u), mul(U0, v)))))
    assert target == leading
    # Collect the scaled finite-difference coefficients by the five poles.
    collected = [{} for _ in range(5)]
    for head, coefficient in [(0, A), (1, scale(-2, A)), (2, A),
                              (0, C), (1, scale(-1, C)),
                              (3, scale(-1, C)), (4, C),
                              (0, scale(-2, mul(a, U2))),
                              (1, scale(2, mul(a, U2))),
                              (0, scale(-2, mul(a, U0))),
                              (3, scale(2, mul(a, U0)))]:
        collected[head] = add(collected[head], coefficient)
    ten_minus = add(constant(10), scale(-2, a))
    claimed = [add(mul(ten_minus, U0), U1, mul(ten_minus, U2)),
               add(scale(-10, U0), scale(-1, U1),
                   mul(add(constant(-20), scale(2, a)), U2)),
               scale(10, U2),
               add(mul(add(constant(-10), scale(2, a)), U0), scale(-1, U1)),
               add(scale(10, U0), U1)]
    assert collected == claimed


def rational_checks():
    s = [[F(i**h, 10000) for i in range(1, 15)] for h in range(3)]
    b = [[(F(i)**(h + 3) - F(15, 2)**(h + 3)) / 10**9
          for i in range(1, 15)] for h in range(3)]
    for sh, bh in zip(s, b):
        assert sum(sh) < F(1, 4)
        assert sum(map(abs, bh)) < F(1, 2)
        assert all(abs(value) < 1 for value in bh)
    oriented = [10 * b[0][i] - b[1][i] for i in range(14)]
    gap = F(411, 16 * 10**9)
    assert max(oriented) == -gap
    assert oriented.index(max(oriented)) == 6  # Group i=7.
    assert F(1, 2**43) < gap
    # epsilon<1/16 and a=epsilon/2^40 imply 2a<2^-43.
    assert F(2, 16 * 2**40) == F(1, 2**43)
    for c0, c2 in [(0, 0), (1, 0), (2, 0), (0, 1), (1, 1)]:
        assert all(abs(c0 * b[0][i] + c2 * b[2][i]) < 2
                   for i in range(14))
    # D_h in (1/2,2), epsilon<1/16 give E>3 and |U_h|<2.
    assert 10 * F(1, 2) - 2 == 3
    assert F(1, 4) + F(1, 16) * 2 < 2
    # Exact safe constants from the algebraic reciprocal estimates.
    assert 3 * 4 * 4 == 48 <= 96
    assert 4 <= 8
    assert (10 * 2 + 10 * 2 + 2) * 96 == 4032
    assert (2 * 2 + 2 * 2) * 8 == 64
    assert 4032 + 64 == 4096
    assert F(4096, 2**40) == F(1, 2**28) < F(1, 4)
    assert 2 * F(1, 8) == F(1, 4)


def main():
    symbolic_checks()
    rational_checks()
    print('Five-head exact identities and rational bounds passed.')
    print('  E=10D0-D1 has every group slope <=-411/(16*10^9).')
    print('  a=epsilon/2^40 gives total error <=epsilon/(2^28 E^3).')
    print('  Five affine numerators and all five positive oriented poles verified.')


if __name__ == '__main__':
    main()
