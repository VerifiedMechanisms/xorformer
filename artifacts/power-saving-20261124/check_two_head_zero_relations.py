#!/usr/bin/env python3
"""Exact finite checks for the two-head zero-relation classification.

These computations illustrate the general written theorem; they do not prove
its quantified statement. No numerical ranks are used.
"""
from itertools import combinations, product
import json
from pathlib import Path
import sympy as sp


def generators(n):
    out = []
    for i in range(n):
        x = [sp.Integer(0)] * (n + 1)
        x[i + 1] = 1
        opposite = x.copy()
        opposite[0] = -1
        out.append((f"x{i+1}", sp.Matrix(x), sp.Matrix(opposite)))
        out.append((f"x{i+1}-1", sp.Matrix(opposite), sp.Matrix(x)))
    for i, j in combinations(range(n), 2):
        difference = [sp.Integer(0)] * (n + 1)
        difference[i + 1], difference[j + 1] = 1, -1
        other = [sp.Integer(0)] * (n + 1)
        other[0], other[i + 1], other[j + 1] = -1, 1, 1
        out.append((f"x{i+1}-x{j+1}", sp.Matrix(difference), sp.Matrix(other)))
        out.append((f"x{i+1}+x{j+1}-1", sp.Matrix(other), sp.Matrix(difference)))
    return out


def check_pair(n, b, c, expected_rank, extra=None):
    x = sp.Matrix([[1, *v] for v in product((0, 1), repeat=n)])
    bv, cv = x * b, x * c
    assert all(z > 0 for z in bv) and all(z > 0 for z in cv)
    # Multiplication by B*C turns A/B+D/C into C*A+B*D.
    matrix = sp.Matrix.hstack(sp.diag(*cv) * x, sp.diag(*bv) * x)
    rank = matrix.rank()
    assert rank == expected_rank, (rank, expected_rank)
    trivial = sp.Matrix.vstack(b, -c)
    assert matrix * trivial == sp.zeros(2**n, 1)
    record = {"B": list(map(str, b)), "C": list(map(str, c)), "rank": rank}
    if extra is not None:
        lam, f, g = extra
        witness = sp.Matrix.vstack(f, -lam * f)
        assert matrix * witness == sp.zeros(2**n, 1)
        assert sp.Matrix.hstack(trivial, witness).rank() == 2
        assert all((x * f)[i] * (x * g)[i] == 0 for i in range(2**n))
        record["extra_kernel_vector"] = list(map(str, witness))
    return record


def main():
    records = []
    for n in (4, 5):
        b = sp.Matrix([1, *range(1, n+1)])
        for name, g, f in generators(n):
            lam, alpha = sp.Integer(1), sp.Rational(1, 7)
            c = lam * b + alpha * g
            record = check_pair(n, b, c, 2 * n, (lam, f, g))
            record.update({"case": name, "n": n})
            records.append(record)
        generic = sp.Matrix([2, *[3, 5, 7, 11, 13][:n]])
        records.append({"case": "generic_positive", "n": n,
                        **check_pair(n, b, generic, 2*n+1)})
        opposite = sp.Matrix([100, *range(-2, -n-2, -1)])
        records.append({"case": "opposite_orientation", "n": n,
                        **check_pair(n, b, opposite, 2*n+1)})
    x1, x2, x3 = sp.symbols("x1 x2 x3")
    B = 1+x1+x2+3*x3
    C = 4+x1+2*x2+3*x3
    A = -14-18*x1-13*x2-18*x3
    D = 56+24*x1+25*x2
    P = sp.expand(A*C+D*B)
    assert P == 6*(x1**2-x1)-(x2**2-x2)-54*(x3**2-x3)
    assert all(P.subs(dict(zip((x1,x2,x3),v))) == 0 for v in product((0,1),repeat=3))
    output = {"status": "all exact rational checks passed", "records": records,
              "three_bit_counterexample_polynomial": str(P)}
    path = Path(__file__).with_name("two-head-zero-relations-exact-check.json")
    path.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"status": output["status"], "cases": len(records), "output": str(path)}))


if __name__ == "__main__":
    main()
