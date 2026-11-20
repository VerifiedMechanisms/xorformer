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


def run(n, h, seed, seconds, out, kind, bound):
    rng = random.Random(seed)
    labels = [rng.choice([-1, 1]) for _ in range(1 << n)]
    if kind == "parity":
        labels = [1-2*(x.bit_count() % 2) for x in range(1 << n)]
    solver = z3.Solver()
    solver.set(timeout=int(1000*seconds), random_seed=seed)
    a = [[z3.Real(f"a_{j}_{i}") for i in range(n+1)] for j in range(h)]
    b = [[z3.RealVal(0)]+[z3.Real(f"b_{j}_{i}") for i in range(1, n+1)] for j in range(h)]
    positive = [[z3.Bool(f"p_{j}_{i}") for i in range(n+1)] for j in range(h)]
    bp, bm = z3.Reals("bias_positive bias_negative")
    parameters = [bp, bm]+sum(a, [])+sum(b, [])
    if bound:
        solver.add(*(z3.And(-bound <= v, v <= bound) for v in parameters))
    solver.add(*(a[j][0] <= a[j+1][0] for j in range(h-1)))
    for x, label in enumerate(labels):
        active = [0]+[i+1 for i in range(n) if x >> i & 1]
        plus, minus = [bp], [bm]
        # A shared artificial exponent below both bias exponents can be used
        # as a finite stand-in for absent terms. It cannot win a comparison.
        floor = z3.If(bp <= bm, bp-1, bm-1)
        for j in range(h):
            d = maximum([b[j][i] for i in active])
            for i in active:
                exponent = a[j][i]-d
                plus.append(z3.If(positive[j][i], exponent, floor))
                minus.append(z3.If(positive[j][i], floor, exponent))
        pp, mm = maximum(plus), maximum(minus)
        solver.add(pp >= mm+1 if label > 0 else mm >= pp+1)
    start = time.monotonic()
    answer = solver.check()
    record = {"n": n, "heads": h, "seed": seed, "labels": kind,
              "seconds": time.monotonic()-start, "answer": str(answer),
              "exponent_bound": bound,
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
            heads.append({"numerator": aa, "denominator": bb})
            exponent_data.append({"a": av, "b": bv, "signs": signs})
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
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.n, args.heads, args.seed, args.seconds, args.out,
        args.labels, args.exponent_bound)
