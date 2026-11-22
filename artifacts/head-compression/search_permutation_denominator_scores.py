#!/usr/bin/env python3
"""Exact full-cube probes of affine permutation denominators.

All labels are fixed before solving. A SAT score must pass both independent
exact checkers. This finite restricted search proves no universal bound.
Use heavy: the mixed integer/real solver may use substantial resources.
"""
import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import random
import time
import z3

from audit_rational_score import audit
from verify_certificate import verify


def rational(model, value):
    result = model.eval(value, model_completion=True)
    assert z3.is_rational_value(result), result
    return Fraction(result.numerator_as_long(), result.denominator_as_long())


def solve(n, heads, seed, seconds, out):
    start = time.monotonic()
    rng = random.Random(seed)
    labels = [rng.choice((-1, 1)) for _ in range(1 << n)]
    (out/"labels.json").write_text(json.dumps(labels)+"\n")
    b = [[z3.Int(f"b_{h}_{i}") for i in range(n)] for h in range(heads)]
    a = [[z3.Real(f"a_{h}_{i}") for i in range(n)] for h in range(heads)]
    bias = z3.Real("bias")
    solver = z3.SolverFor("QF_LIRA")
    solver.set(timeout=max(1, int(seconds*1000)), random_seed=seed)
    for row in b:
        for value in row:
            solver.add(value >= 1-heads, value <= heads-1)
    for i in range(n):
        solver.add(z3.Sum(*[row[i] for row in b]) == 0)
    for vertex, label in enumerate(labels):
        indices = [i for i in range(n) if (vertex >> i) & 1]
        if not indices:
            solver.add(label*bias >= 1)
            continue
        common = (heads+1)*(1+len(indices))
        poles = [h+1+z3.Sum(*[b[h][i] for i in indices]) for h in range(heads)]
        solver.add(z3.Distinct(*poles))
        values = []
        for h in range(heads):
            value = z3.Real(f"v_{vertex}_{h}")
            numerator = z3.Sum(*[a[h][i] for i in indices])
            solver.add(z3.Or(*[z3.And(poles[h] == k,
                                     (common+k)*value == numerator)
                               for k in range(1, heads+1)]))
            values.append(value)
        solver.add(label*(bias+z3.Sum(*values)) >= 1)
    print(json.dumps({"event": "solver-start", "n": n, "heads": heads,
                      "seed": seed, "vertices": len(labels),
                      "timeout_seconds": seconds}), flush=True)
    status = solver.check()
    record = {"n": n, "heads": heads, "seed": seed, "status": str(status),
              "seconds": time.monotonic()-start,
              "scope": "One fixed full-cube target in the affine permutation family.",
              "unrestricted_lower_bound": False, "target_proved": False}
    if status == z3.sat:
        model = solver.model()
        slopes = [[model.eval(v).as_long() for v in row] for row in b]
        for vertex in range(1 << n):
            values = [h+1+sum(slopes[h][i] for i in range(n) if (vertex >> i) & 1)
                      for h in range(heads)]
            assert sorted(values) == list(range(1, heads+1))
        fractions = []
        for h in range(heads):
            numerator = [Fraction(0)]+[rational(model, v) for v in a[h]]
            denominator = [heads+h+2]+[heads+1+v for v in slopes[h]]
            assert min(denominator) > 0
            scale = math.lcm(*(v.denominator for v in numerator))
            fractions.append({"numerator": [int(v*scale) for v in numerator],
                              "denominator": [v*scale for v in denominator]})
        c = rational(model, bias)
        certificate = {"n": n, "labels": labels, "heads": fractions,
                       "bias": [c.numerator, c.denominator],
                       "scope": "This finite truth table only; no universal bound.",
                       "permutation_denominators": {"integer_slopes": slopes,
                         "pole_list": list(range(1, heads+1)),
                         "common_form": [heads+1]*(n+1)}}
        path = out/"certificate.json"
        path.write_text(json.dumps(certificate)+"\n")
        integer_audit = audit(path, 224)
        assert integer_audit["all_target_signs_certified"]
        fraction_audit = verify(path)
        (out/"integer-audit.json").write_text(json.dumps(integer_audit, indent=2)+"\n")
        (out/"fraction-audit.json").write_text(json.dumps(fraction_audit, indent=2)+"\n")
        record.update(certificate="certificate.json", all_vertices_permutation_checked=True,
                      exact_signs_checked=True, certificate_sha256=integer_audit["input_sha256"])
    elif status == z3.unknown:
        record["reason_unknown"] = solver.reason_unknown()
    (out/"result.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps(record), flush=True)
    return record


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--smoke", action="store_true")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    cases = [(3, 4, 60)] if args.smoke else [(4, 5, 300), (5, 6, 1200),
                                            (6, 8, 3600), (7, 10, 7200),
                                            (8, 16, 10800)]
    records = []
    for n, heads, seconds in cases:
        out = args.out/f"n{n}-h{heads}"
        out.mkdir(exist_ok=True)
        records.append(solve(n, heads, 2026112200+n, seconds, out))
        (args.out/"results.json").write_text(json.dumps(records, indent=2)+"\n")
