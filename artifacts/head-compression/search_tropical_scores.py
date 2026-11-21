#!/usr/bin/env python3
"""Search for an exactly liftable dominant-term construction using SMT.

Each affine coefficient is a signed integral power of a common integer base.
Denominator coefficients are positive. An SMT model is lifted to an ordinary
admissible rational score and independently checked. UNSAT concerns this
restricted dominance ansatz only, never all admissible head representations.
Run through heavy.
"""
import argparse
from fractions import Fraction
import json
from math import lcm
from pathlib import Path
import random
import time
import z3
from search_sign_scores import exact_check


def maximum(values):
    result = values[0]
    for value in values[1:]:
        result = z3.If(result >= value, result, value)
    return result


def integer_pair(aa, bb):
    denominator = lcm(*(v.denominator for v in aa+bb))
    return ([int(v*denominator) for v in aa],
            [int(v*denominator) for v in bb])


def run(n, h, seed, seconds, out, kind, bound, mixed_orientations=False,
        parity_coordinate_symmetry=False):
    rng = random.Random(seed)
    labels = [rng.choice([-1, 1]) for _ in range(1 << n)]
    if kind == "parity":
        labels = [1-2*(x.bit_count() % 2) for x in range(1 << n)]
    solver = z3.Solver()
    solver.set(timeout=int(1000*seconds), random_seed=seed)
    a = [[z3.Real(f"a_{j}_{i}") for i in range(n+1)] for j in range(h)]
    b = [[z3.RealVal(0)]+[z3.Real(f"b_{j}_{i}") for i in range(1, n+1)] for j in range(h)]
    positive = [[z3.Bool(f"p_{j}_{i}") for i in range(n+1)] for j in range(h)]
    orientation = [z3.Bool(f"forward_{j}") if mixed_orientations else
                   z3.BoolVal(True) for j in range(h)]
    bp, bm = z3.Reals("bias_positive bias_negative")
    parameters = [bp, bm]+sum(a, [])+sum(b, [])
    if bound:
        solver.add(*(z3.And(-bound <= v, v <= bound) for v in parameters))
    solver.add(*(a[j][0] <= a[j+1][0] for j in range(h-1)))
    if parity_coordinate_symmetry:
        assert kind == "parity"
        # Coordinate permutations preserve parity. After head ordering, the
        # first head's denominator slopes can therefore be ordered as well.
        solver.add(*(b[0][i] <= b[0][i+1] for i in range(1, n)))
    for x, label in enumerate(labels):
        plus, minus = [bp], [bm]
        # A shared artificial exponent below both bias exponents can be used
        # as a finite stand-in for absent terms. It cannot win a comparison.
        floor = z3.If(bp <= bm, bp-1, bm-1)
        for j in range(h):
            active = [z3.BoolVal(True)]+[
                orientation[j] == z3.BoolVal(bool(x >> i & 1))
                for i in range(n)]
            # b[j][0] is zero, so -1 safely replaces an absent term here.
            d = maximum([z3.If(active[i], b[j][i], -1)
                         for i in range(n+1)])
            for i in range(n+1):
                exponent = a[j][i]-d
                plus.append(z3.If(z3.And(active[i], positive[j][i]), exponent, floor))
                minus.append(z3.If(z3.And(active[i], z3.Not(positive[j][i])), exponent, floor))
        pp, mm = maximum(plus), maximum(minus)
        solver.add(pp >= mm+1 if label > 0 else mm >= pp+1)
    start = time.monotonic()
    answer = solver.check()
    record = {"n": n, "heads": h, "seed": seed, "labels": kind,
              "seconds": time.monotonic()-start, "answer": str(answer),
              "exponent_bound": bound,
              "mixed_orientations": mixed_orientations,
              "parity_coordinate_symmetry": parity_coordinate_symmetry,
              "scope": "Restricted dominant-term ansatz on one finite truth table."}
    if answer == z3.unknown:
        record["reason"] = solver.reason_unknown()
    if answer == z3.sat:
        model = solver.model()
        def rational(v):
            q = model.eval(v, model_completion=True)
            return Fraction(q.numerator_as_long(), q.denominator_as_long())
        scale = lcm(*(rational(v).denominator for v in parameters))
        exponent = lambda v: int(scale*rational(v))
        # At most h*(n+1)+1 terms oppose the winner. Each denominator has
        # at most n+1 active positive monomials, so this base makes its
        # winning contribution larger than their sum.
        base = 2*(n+1)*(h*(n+1)+1)
        power = lambda e: Fraction(base)**e
        heads = []
        exponent_data = []
        for j in range(h):
            av, bv = [exponent(v) for v in a[j]], [exponent(v) for v in b[j]]
            signs = [1 if z3.is_true(model.eval(v, model_completion=True)) else -1
                     for v in positive[j]]
            aa, bb = integer_pair([s*power(e) for s, e in zip(signs, av)],
                                  [power(e) for e in bv])
            forward = z3.is_true(model.eval(orientation[j], model_completion=True))
            if not forward:
                # Convert from (1,1-x_1,...,1-x_n) to ordinary affine forms.
                aa = [sum(aa)]+[-v for v in aa[1:]]
                bb = [sum(bb)]+[-v for v in bb[1:]]
            heads.append({"numerator": aa, "denominator": bb})
            exponent_data.append({"a": av, "b": bv, "signs": signs,
                                  "forward": forward})
        bias = power(exponent(bp))-power(exponent(bm))
        cert = {"n": n, "labels": labels, "heads": heads,
                "bias": [bias.numerator, bias.denominator],
                "scope": "This finite truth table only; not a universal upper bound."}
        check = exact_check(cert)
        assert check["certified"], check
        cert["verification"] = check
        (out/"certificate.json").write_text(json.dumps(cert)+"\n")
        (out/"exponents.json").write_text(json.dumps({"base": base,
             "heads": exponent_data, "bias": [exponent(bp), exponent(bm)]})+"\n")
        record["certificate"] = "certificate.json"
    (out/"result.json").write_text(json.dumps(record)+"\n")
    print(json.dumps(record), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--heads", type=int, required=True)
    parser.add_argument("--seed", type=int, default=150000)
    parser.add_argument("--seconds", type=float, default=3600)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--labels", choices=["random", "parity"], default="random")
    parser.add_argument("--exponent-bound", type=int, default=0)
    parser.add_argument("--mixed-orientations", action="store_true")
    parser.add_argument("--parity-coordinate-symmetry", action="store_true")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.n, args.heads, args.seed, args.seconds, args.out,
        args.labels, args.exponent_bound, args.mixed_orientations,
        args.parity_coordinate_symmetry)
