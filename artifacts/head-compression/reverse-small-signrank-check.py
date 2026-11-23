#!/usr/bin/env python3
"""A completely rational 5 by 32 reverse grid with two heads.

The row constants come from reverse-joint-five-row.tex.  Instead of an
inverse function theorem or numerical inverse, take one explicit rational
step in the inverse-Jacobian direction.  The cleared scores are quadratic,
so an exact remainder bound determines the step size.  This checks a finite
example, not an asymptotic sign-rank theorem or a universal compiler.
"""

from itertools import product

import sympy as sp


def main():
    columns = 32
    eps = sp.Rational(1, 100 * (columns + 1))
    slopes = ((5, 6), (6, 8), (7, 5), (9, 7), (8, 11))
    rows = (
        (-3, -5),
        (-(37 * eps - 4) / (17 * eps - 2),
         -3 * (35 * eps - 4) / (17 * eps - 2)),
        (-3 * (31 * eps - 4) / (15 * eps - 2),
         -(33 * eps - 4) / (15 * eps - 2)),
        (-3 * (39 * eps - 4) / (19 * eps - 2),
         -(41 * eps - 4) / (19 * eps - 2)),
        (-(2250 * eps**3 - 625 * eps**2 + 61 * eps - 2)
         / (2 * eps * (11 * eps - 1)),
         (2964 * eps**3 - 949 * eps**2 + 83 * eps - 2)
         / (2 * eps * (11 * eps - 1))),
    )

    def cleared(i, point):
        u, v, a, b = point
        c, k = slopes[i]
        A, B = rows[i]
        return (A + a) * (1 - k * eps - v) + (B + b) * (1 - c * eps - u)

    points, targets = [], []
    for tau in (-1, 1):
        base = sp.Matrix((eps, 2 * eps, 3, 5) if tau == 1
                         else (2 * eps, eps, 5, 3))
        u, v, a, b = base
        jac = sp.Matrix([
            [-B - b, -A - a, 1 - k * eps - v, 1 - c * eps - u]
            for (c, k), (A, B) in zip(slopes[:4], rows[:4])
        ])
        assert jac.det() != 0
        inverse = jac.inv()
        assert all(cleared(i, base) == 0 for i in range(4))
        initial_fifth = cleared(4, base)
        assert tau * initial_fifth > 0
        c, k = slopes[4]
        A, B = rows[4]
        fifth_gradient = sp.Matrix([[-B - b, -A - a,
                                     1 - k * eps - v, 1 - c * eps - u]])
        for signs in product((-1, 1), repeat=4):
            direction = inverse * sp.Matrix(signs)
            du, dv, da, db = direction
            quadratic = -da * dv - db * du
            fifth_linear = (fifth_gradient * direction)[0]
            # Every denominator is rational and positive.  The added 1
            # handles vanishing derivative/remainder coefficients uniformly.
            step = min(
                sp.Rational(1, 2),
                eps / (4 * (1 + abs(du) + abs(dv))),
                1 / (4 * (1 + abs(quadratic))),
                abs(initial_fifth)
                / (4 * (1 + abs(fifth_linear) + abs(quadratic))),
            )
            point = base + step * direction
            assert eps / 2 < point[0] < 5 * eps / 2
            assert eps / 2 < point[1] < 5 * eps / 2
            for i, sign in enumerate(signs):
                assert cleared(i, point) == step * sign + step**2 * quadratic
                assert sign * cleared(i, point) > 0
            assert tau * cleared(4, point) > 0
            points.append(point)
            targets.append(signs + (tau,))

    assert len(set(targets)) == 32
    # Negative slopes make the all-ones vertex the global minimum.
    minima = [1 - sum(c for c, _ in slopes) * eps - sum(p[0] for p in points),
              1 - sum(k for _, k in slopes) * eps - sum(p[1] for p in points)]
    assert all(value > 0 for value in minima)
    assert all(value > sp.Rational(9, 10) for value in minima)
    print("Exact rational certificate: all 32 five-bit columns verified.")
    print("Both whole-cube denominator minima exceed 9/10; all slopes are strict.")
    print("The resulting 5 by 32 sign matrix has sign-rank exactly 5.")
    print("Scope: two heads refute a 2H sign-rank cap, not an O(H) cap.")


if __name__ == "__main__":
    main()
