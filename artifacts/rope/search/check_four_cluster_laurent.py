#!/usr/bin/env python3
"""Exact finite search for four-pole Laurent collisions.

Run as ``heavy python3 artifacts/rope/search/check_four_cluster_laurent.py``.
The four poles are zero and one of eleven prescribed triples. Residues are
homogeneous linear forms in x,y,z,w with rational Laurent coefficients from
t^-12 through t^0. The residue at zero cancels the zeroth moment exactly.
We require bounded first/second moments and a third moment tending to zero.
This checks the entire finite linear ansatz, not arbitrary collision paths.
"""

import argparse
import json
from pathlib import Path

import sympy as sp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-pole", type=int, default=12)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".exact.json"))
    args = parser.parse_args()
    assert args.max_pole >= 1
    t = sp.Symbol("t")
    coordinates = sp.symbols("x y z w")
    x, y, z, _ = coordinates
    cases = {
        "A": [t*x, 2*t*x+t**2*y, 3*t*x+3*t**2*y+t**3*z],
        "B": [t*x, t*x+t**2*y, 2*t*x+t**3*z],
        "C": [t*x, t*y, t*(x+y)+t**2*z],
        "D": [t*x, t*y, t*z],
        "E": [t*x, t**2*y, t**3*z],
        "F": [t*x, 2*t*x+t**3*y, 3*t*x+3*t**3*y+t**4*z],
        "G": [t*x, t*x+t**2*y, t*x+t**2*y+t**3*z],
        "H": [t**2*x, 2*t**2*x+t**3*y, 3*t**2*x+3*t**3*y+t**4*z],
        "I": [t**2*x, 2*t**2*x+t**3*y, 3*t**2*x+t**3*z],
        "J": [t**2*y, t*x, t*x+t**2*z],
        "K": [t**3*x, 2*t**3*x+t**4*y, 3*t**3*x+3*t**4*y+t**5*z],
    }
    columns = [(i, e, l) for i in range(3)
               for e in range(-args.max_pole, 1) for l in range(4)]
    results = []
    for name, roots in cases.items():
        constraints, outputs = {}, {}
        for degree in (1, 2, 3):
            for column, (i, exponent, variable) in enumerate(columns):
                polynomial = sp.Poly(roots[i]**degree * coordinates[variable],
                                     t, *coordinates)
                for powers, coefficient in polynomial.terms():
                    power = powers[0] + exponent
                    monomial = powers[1:]
                    if power < 0 or (degree == 3 and power == 0):
                        constraints.setdefault((degree, power, monomial), {})[column] = coefficient
                    elif degree == 2 and power == 0:
                        outputs.setdefault(monomial, {})[column] = coefficient

        def matrix(rows):
            value = sp.MutableSparseMatrix(len(rows), len(columns), {})
            for row_index, row in enumerate(rows.values()):
                for column, coefficient in row.items():
                    value[row_index, column] = coefficient
            return value

        constraint_matrix, output_matrix = matrix(constraints), matrix(outputs)
        kernel = constraint_matrix.nullspace()
        images = [output_matrix * vector for vector in kernel]
        image_basis = sp.Matrix.hstack(*images).columnspace() if images else []
        monomials = [sp.prod(variable**power for variable, power in zip(coordinates, monomial))
                     for monomial in outputs]
        cubic_basis = [sp.expand(sum(a*b for a, b in zip(vector, monomials)))
                       for vector in image_basis]
        parameters = sp.symbols(f"c0:{len(cubic_basis)}")
        generic_cubic = sum(c*p for c, p in zip(parameters, cubic_basis))
        derivatives = [sp.Poly(sp.diff(generic_cubic, variable), *coordinates)
                       for variable in coordinates]
        derivative_monomials = sorted({monomial for polynomial in derivatives
                                       for monomial, _ in polynomial.terms()})
        derivative_matrix = sp.Matrix([
            [polynomial.coeff_monomial(monomial) for polynomial in derivatives]
            for monomial in derivative_monomials])
        rank = derivative_matrix.rank()
        result = {
            "case": name,
            "nonzero_roots": list(map(str, roots)),
            "constraint_matrix_shape": list(constraint_matrix.shape),
            "kernel_dimension": len(kernel),
            "limiting_second_moment_basis": list(map(str, cubic_basis)),
            "generic_essential_variable_count": rank,
        }
        results.append(result)
        print(f"{name}: image dimension {len(cubic_basis)}, generic derivative rank {rank}", flush=True)
        assert rank <= 3, f"A finite-ansatz counterexample was found in case {name}"
    payload = {
        "scope": "Eleven specified root triples; homogeneous linear residues in four variables; no universal conclusion.",
        "max_residue_pole": args.max_pole,
        "arithmetic": "exact rational linear algebra and symbolic polynomial derivative ranks",
        "sympy_version": sp.__version__,
        "results": results,
    }
    args.output.write_text(json.dumps(payload, indent=2) + "\n")


if __name__ == "__main__":
    main()
