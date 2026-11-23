#!/usr/bin/env python3
"""Exact certificates for the five-row regular-sheet constructions.

Requires SymPy. Every check is symbolic rational arithmetic or an exact
rational specialization. No floating-point values or numerical solver
are used. The first part verifies identities in the indeterminate eps,
not merely at a finite collection of eps values.
"""

import sympy as sp


eps, u, v, a, b = sp.symbols("eps u v a b")
aa, bb = sp.symbols("aa bb")
parameters = (u, v, a, b)
sheets = (
    {u: eps, v: 2 * eps, a: 3, b: 5},
    {u: 2 * eps, v: eps, a: 5, b: 3},
)
row_slopes = ((5, 6), (6, 8), (7, 5), (9, 7), (8, 11))


def zero(expression):
    assert sp.cancel(expression) == 0, sp.factor(expression)


def residue(expression, prime=101):
    value = sp.cancel(expression.subs(eps, sp.Rational(1, 1000)))
    assert value.is_Rational
    numerator, denominator = map(int, value.as_numer_denom())
    assert denominator % prime != 0
    return numerator * pow(denominator, -1, prime) % prime


def certify_original_gadget():
    row_numerators = (
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
    scores, cleared, denominator_products = [], [], []
    for (c, k), (row_a, row_b) in zip(row_slopes, row_numerators):
        d, e = 1 - c * eps, 1 - k * eps
        scores.append((row_a + a) / (d - u) + (row_b + b) / (e - v))
        cleared.append((row_a + a) * (e - v) + (row_b + b) * (d - u))
        denominator_products.append((d - u) * (e - v))

    for sheet_index, sheet in enumerate(sheets):
        for row_index, score in enumerate(scores):
            expected = 0 if row_index < 4 else (1 if sheet_index == 0 else -1)
            zero(score.subs(sheet) - expected)

    delta = (96 * eps**3 * (337 * eps**2 - 74 * eps + 4)
             / ((15 * eps - 2) * (17 * eps - 2) * (19 * eps - 2)))
    jacobian = sp.Matrix(cleared[:4]).jacobian(parameters)
    rational_jacobian = sp.Matrix(scores[:4]).jacobian(parameters)
    for sheet_index, sheet in enumerate(sheets):
        sign = 1 if sheet_index == 0 else -1
        zero(jacobian.subs(sheet).det() - sign * delta)
        # At a common zero, differentiating G_i = denominator_i * F_i
        # removes the product-rule term involving F_i itself.
        for i in range(4):
            for j in range(4):
                zero((jacobian[i, j]
                      - denominator_products[i] * rational_jacobian[i, j]).subs(sheet))
    print("Original gadget: all 10 sheet-value identities and both full Jacobian "
          "determinant formulas verified identically in eps.")


def certify_axis_subtracted_resynthesis():
    scores, system_determinants = [], []
    for row_index, (c, k) in enumerate(row_slopes):
        d, e = 1 - c * eps, 1 - k * eps
        score = ((aa + a) / (d - u) - aa / d - a / (1 - u)
                 + (bb + b) / (e - v) - bb / e - b / (1 - v))
        equations = [score.subs(sheet) for sheet in sheets]
        if row_index == 4:
            equations[0] -= 1
            equations[1] += 1
        coefficient_matrix, rhs = sp.linear_eq_to_matrix(equations, (aa, bb))
        system_determinants.append(sp.cancel(coefficient_matrix.det()))
        solution = coefficient_matrix.inv() * rhs
        score = score.subs({aa: sp.cancel(solution[0]), bb: sp.cancel(solution[1])})
        scores.append(score)
        for sheet_index, sheet in enumerate(sheets):
            expected = 0 if row_index < 4 else (1 if sheet_index == 0 else -1)
            zero(score.subs(sheet) - expected)

    jacobian = sp.Matrix(scores[:4]).jacobian(parameters)
    jacobian_residues = []
    for sheet in sheets:
        matrix = jacobian.subs(sheet).subs(eps, sp.Rational(1, 1000))
        # Reduction is valid entrywise, and so certifies a nonzero
        # rational determinant at this exact specialization.
        reduced = sp.Matrix([[residue(entry) for entry in row] for row in matrix.tolist()])
        jacobian_residues.append(int(reduced.det()) % 101)
        assert jacobian_residues[-1] != 0
    system_residues = [residue(value, 103) for value in system_determinants]
    assert all(system_residues)
    assert system_residues == [92, 36, 64, 69, 13]
    assert jacobian_residues == [40, 69]
    print("Axis-subtracted resynthesis: all 10 sheet-value identities verified "
          "identically in eps.")
    print("At eps=1/1000, coefficient-system determinants modulo 103:", system_residues)
    print("At eps=1/1000, both four-query Jacobian determinants modulo 101:", jacobian_residues)
    print("All these rational functions are therefore nonzero identically; "
          "only finitely many eps values can be excluded.")


if __name__ == "__main__":
    certify_original_gadget()
    certify_axis_subtracted_resynthesis()
