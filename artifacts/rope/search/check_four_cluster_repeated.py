#!/usr/bin/env python3
"""Exact finite search for four-pole collisions with repeated or higher-order leading roots.

Run as ``heavy python3 artifacts/rope/search/check_four_cluster_repeated.py``.
The four poles are zero and one of twelve prescribed triples. Residues are
homogeneous linear forms in x,y,z,w with rational Laurent coefficients from
t^-15 through t^0. The residue at zero cancels the zeroth moment exactly.
We require bounded first/second moments and a third moment tending to zero.
This checks the entire finite linear ansatz, not arbitrary collision paths.
"""

import argparse
import json
from pathlib import Path

import sympy as sp


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-pole", type=int, default=15)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".exact.json"))
    args = parser.parse_args()
    assert args.max_pole >= 1
    t = sp.Symbol("t")
    coordinates = sp.symbols("x y z w")
    x, y, z, _ = coordinates
    w = coordinates[3]
    cases = {
        "R1": [t*x, t*x+t**2*y, t*x+t**2*z],
        "R2": [t*x, t*x+t**2*y, t*x+2*t**2*y+t**3*z],
        "R3": [t*x+t**2*y, t*x+t**2*z, t*x+t**2*w],
        "R4": [t*x, t*x+t**2*y+t**3*z, t*x+2*t**2*y+t**3*w],
        "R5": [t*x, t*x+t**3*y, t*x+t**3*y+t**5*z],
        "R6": [t*x, t*x+t**4*y, 2*t*x+t**3*z],
        "R7": [t**2*x, -t**2*x+t**3*y, t**4*z],
        "R8": [t**3*x, 2*t**3*x+t**4*y, 3*t**3*x+t**4*z+t**5*w],
        "R9": [t**2*x+t**3*y, t**2*x+t**4*z, 2*t**2*x+t**3*y+t**5*w],
        "R10": [t**4*x, t**4*x+t**5*y, t**4*x+2*t**5*y+t**6*z],
        "R11": [t*x, -t*x+t**2*y, t**2*z+t**3*w],
        "R12": [t**2*x+t**3*y, -t**2*x+t**4*z, t**3*w],
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
        "scope": "Twelve specified repeated or higher-order root triples; homogeneous linear residues in four variables; no universal conclusion.",
        "max_residue_pole": args.max_pole,
        "arithmetic": "exact rational linear algebra and symbolic polynomial derivative ranks",
        "sympy_version": sp.__version__,
        "results": results,
    }
    args.output.write_text(json.dumps(payload, indent=2) + "\n")


if __name__ == "__main__":
    main()
