#!/usr/bin/env python3
"""Exact-real feasibility probes for a fixed-direction compact rowcube decoder.

This is a finite experiment, not a universality proof. Denominators are
b_h + sum_i d_hi x_i with fixed strictly positive rational d_hi, and each
offset is restricted to 1 < b_h < 1 + 1/8. Numerator constants and bias vary.
All cube denominators are therefore strictly positive. A positive common
denominator product converts strict signs to polynomial inequalities.

Run solver experiments through `heavy`, as required on this shared machine.
"""

import argparse
import itertools
import json
import random
import time
from fractions import Fraction

import z3


def solve(directions, labels, timeout_ms):
    heads = len(directions)
    dimension = len(directions[0])
    offsets = [z3.Real(f"b_{h}") for h in range(heads)]
    residues = [z3.Real(f"a_{h}") for h in range(heads)]
    bias = z3.Real("bias")
    solver = z3.SolverFor("QF_NRA")
    solver.set(timeout=timeout_ms)
    for offset in offsets:
        solver.add(offset > 1, offset < z3.RealVal("9/8"))
    for bits, label in zip(itertools.product((0, 1), repeat=dimension), labels):
        denominators = [
            offsets[h] + sum(z3.RealVal(str(d)) * x for d, x in zip(directions[h], bits))
            for h in range(heads)
        ]
        product = z3.Product(denominators)
        cleared = bias * product + sum(
            residues[h] * z3.Product(denominators[:h] + denominators[h + 1 :])
            for h in range(heads)
        )
        solver.add(label * cleared >= 1)
    started = time.monotonic()
    result = solver.check()
    out = {"status": str(result), "seconds": time.monotonic() - started}
    if result == z3.sat:
        model = solver.model()
        out["offsets"] = [str(model.eval(v, model_completion=True)) for v in offsets]
        out["residues"] = [str(model.eval(v, model_completion=True)) for v in residues]
        out["bias"] = str(model.eval(bias, model_completion=True))
        try:
            bb = list(map(Fraction, out["offsets"]))
            aa = list(map(Fraction, out["residues"]))
            tau = Fraction(out["bias"])
            dd = [[Fraction(str(d)) for d in row] for row in directions]
            margin = None
            for bits, label in zip(itertools.product((0, 1), repeat=dimension), labels):
                den = [bb[h] + sum(d*x for d, x in zip(dd[h], bits))
                       for h in range(heads)]
                assert all(d > 0 for d in den)
                value = label * (tau + sum(a/d for a, d in zip(aa, den)))
                assert value > 0
                margin = value if margin is None else min(margin, value)
            assert all(Fraction(1) < b < Fraction(9, 8) for b in bb)
            out["rational_recheck"] = True
            out["minimum_strict_margin"] = str(margin)
        except ValueError:
            out["rational_recheck"] = False
            out["rational_recheck_reason"] = "solver witness contains an algebraic number"
    elif result == z3.unknown:
        out["reason"] = solver.reason_unknown()
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dimension", type=int, default=3)
    parser.add_argument("--heads", type=int, default=3)
    parser.add_argument("--random-targets", type=int, default=3)
    parser.add_argument("--timeout-ms", type=int, default=10000)
    parser.add_argument("--seed", type=int, default=2403)
    parser.add_argument("--uniform", action="store_true")
    parser.add_argument("--all-targets", action="store_true")
    parser.add_argument("--epsilon", type=Fraction)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    directions = [
        [1] * args.dimension
        if args.uniform or h == 0
        else [(h + 1) ** i for i in range(args.dimension)]
        for h in range(args.heads)
    ]
    if args.epsilon is not None:
        directions = [[str(1 + args.epsilon * ((h + 1) ** i - 1))
                       for i in range(args.dimension)] for h in range(args.heads)]
    inputs = list(itertools.product((0, 1), repeat=args.dimension))
    targets = [("parity", [(-1) ** sum(x) for x in inputs])]
    if args.all_targets:
        targets = [(f"table_{r}", list(labels)) for r, labels in
                   enumerate(itertools.product((-1, 1), repeat=len(inputs)))
                   if labels[0] == 1]
    else:
        for r in range(args.random_targets):
            targets.append((f"random_{r}", [rng.choice((-1, 1)) for _ in inputs]))
    print(json.dumps({"dimension": args.dimension, "heads": args.heads,
                      "directions": directions, "offset_interval": ["1", "9/8"]}), flush=True)
    for name, labels in targets:
        print(json.dumps({"target": name, "labels": labels,
                          **solve(directions, labels, args.timeout_ms)}), flush=True)


if __name__ == "__main__":
    main()
