#!/usr/bin/env python3
"""Exact finite screen for a proposed confluent sign-compatibility lemma.

Requires pplpy. This is not a proof for arbitrary sizes or all word sets.
Run as: heavy env PYTHONPATH=/tmp/joint-ppl python3 this-file.py ...
"""
import argparse
from fractions import Fraction as F
from functools import reduce
from math import lcm
import json
import random
import ppl


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--points", type=int, default=8)
    ap.add_argument("--words", type=int, default=3)
    ap.add_argument("--features", type=int, default=3)
    ap.add_argument("--trials", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--output")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    q, r, d = args.points, args.words, args.features
    poles = [F(j, 2*q) for j in range(q)]
    queries = [2 + F(i, 2*q) for i in range(q)]
    kernels = [[[(queries[i] - poles[j]) ** (-m-2) for m in range(d)]
                for j in range(q)] for i in range(q)]
    record = {"status": "exact finite feasibility screen only", "arguments": vars(args),
              "poles": list(map(str, poles)), "queries": list(map(str, queries)), "trials": []}
    for trial in range(args.trials):
        word = [[rng.choice([-1, 1]) for t in range(r)] for i in range(q)]
        poly = ppl.C_Polyhedron(q*d, "universe")
        rows = []
        for i in range(q):
            for t in range(r):
                row = [word[i][t] * word[j][t] * kernels[i][j][m]
                       for j in range(q) for m in range(d)]
                scale = reduce(lcm, [v.denominator for v in row], 1)
                integer_row = [int(v * scale) for v in row]
                poly.add_constraint(sum(v * ppl.Variable(k) for k, v in enumerate(integer_row)) >= scale)
                rows.append(row)
        feasible = not poly.is_empty()
        item = {"trial": trial, "feasible": feasible, "word": word}
        if feasible:
            point = next(g for g in poly.minimized_generators() if g.is_point())
            coeff = [F(int(point.coefficient(ppl.Variable(k))), int(point.divisor()))
                     for k in range(q*d)]
            margins = [sum(x*y for x, y in zip(row, coeff)) for row in rows]
            assert min(margins) >= 1
            item["coefficient"] = list(map(str, coeff))
            item["minimum_margin"] = str(min(margins))
        record["trials"].append(item)
        print(json.dumps({"trial": trial, "feasible": feasible}), flush=True)
        if not feasible:
            break
    if args.output:
        with open(args.output, "w") as f:
            json.dump(record, f, indent=2)


if __name__ == "__main__":
    main()
