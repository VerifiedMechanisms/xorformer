#!/usr/bin/env python3
"""Exact finite audit of the five-row reader in continuation-three-head-reader.tex.

This checks rational strict witnesses, not an asymptotic bound or Lean proof.
"""
from itertools import combinations
import json
import sympy as sp


def audit():
    u = sp.Matrix([1, 2, 3, 4, 5])
    one = sp.ones(5, 1)
    square = u.applyfunc(lambda x: x*x)
    raw = [sp.Matrix(v) for v in (
        (0, 0, -2, -2, -1), (0, 0, -2, 1, -2), (0, 0, -2, 1, 2))]
    coefficients = sp.Matrix.hstack(one, u, *raw).inv() * (3*square)
    assert list(coefficients) == [-6, 9, -7, -sp.Rational(21, 4), sp.Rational(37, 4)]
    normalized = [coefficients[k+2]*raw[k] for k in range(3)]
    normalized[2] += coefficients[0]*one + coefficients[1]*u
    perturbations = [sp.Rational(2, 3)*(square-v) for v in normalized]
    assert sum(normalized, sp.zeros(5, 1)) == 3*square
    assert sum(perturbations, sp.zeros(5, 1)) == sp.zeros(5, 1)
    assert [list(v) for v in perturbations] == [
        [sp.Rational(2, 3), sp.Rational(8, 3), -sp.Rational(10, 3), sp.Rational(4, 3), 12],
        [sp.Rational(2, 3), sp.Rational(8, 3), -1, sp.Rational(85, 6), sp.Rational(29, 3)],
        [-sp.Rational(4, 3), -sp.Rational(16, 3), sp.Rational(13, 3), -sp.Rational(31, 2), -sp.Rational(65, 3)]]
    planes = [sp.Matrix.hstack(one, u, f) for f in raw]
    gales = [sp.Matrix(g) for g in (
        ((1, -1, -1, 1, 0), (5, -6, -1, 0, 2)),
        ((5, -8, 1, 2, 0), (2, -2, -1, 0, 1)),
        ((5, -8, 1, 2, 0), (4, -6, 1, 0, 1)))]
    for plane, gale in zip(planes, gales):
        assert plane.rank() == 3 and gale.rank() == 2
        assert gale*plane == sp.zeros(2, 3)
    usage = [0, 0, 0]
    witnesses = []
    for word in range(32):
        signs = [1 if word >> i & 1 else -1 for i in range(5)]
        for template, gale in enumerate(gales):
            signed = gale*sp.diag(*signs)
            target = -signed*sp.ones(5, 1)
            for first, second in combinations(range(5), 2):
                pair = signed[:, [first, second]]
                if pair.det() == 0:
                    continue
                addition = pair.inv()*target
                if min(addition) < 0:
                    continue
                positive = sp.ones(5, 1)
                positive[first] += addition[0]
                positive[second] += addition[1]
                output = sp.diag(*signs)*positive
                assert gale*output == sp.zeros(2, 1)
                coords = planes[template].gauss_jordan_solve(output)[0]
                assert min(sp.diag(*signs)*planes[template]*coords) >= 1
                usage[template] += 1
                witnesses.append((word, template, [str(x) for x in coords]))
                break
            else:
                continue
            break
        else:
            raise AssertionError(f"Uncovered strict word {word}")
    assert usage == [22, 6, 4]
    return {"strict_words": len(witnesses), "template_usage": usage}


if __name__ == "__main__":
    print(json.dumps(audit()))
