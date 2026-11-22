#!/usr/bin/env python3
"""Search affine cubes whose vertex vectors permute a fixed integer list.

This tests a structural hypothesis about a restricted denominator family.
SAT witnesses are checked by independent integer enumeration. An UNSAT or
timeout result here is not a lower bound for the unrestricted head model.
Run through heavy, including small solver experiments on a shared machine.
"""
import argparse
import itertools
import json
from pathlib import Path
import time
import z3


def verify(n, poles, slopes):
    assert len(slopes) == len(poles)
    assert all(len(row) == n for row in slopes)
    vertices = []
    for bits in itertools.product((0, 1), repeat=n):
        values = [a + sum(b*x for b, x in zip(row, bits))
                  for a, row in zip(poles, slopes)]
        assert sorted(values) == sorted(poles), (bits, values)
        vertices.append(dict(bits=bits, values=values))
    support = [sum(v != 0 for v in row) for row in slopes]
    assert max(support) == n
    return dict(vertices=vertices, row_supports=support,
                all_vertices_checked=True)


def solve(n, size, timeout):
    start = time.monotonic()
    poles = list(range(1, size+1))
    b = [[z3.Int(f"b_{h}_{i}") for i in range(n)] for h in range(size)]
    solver = z3.SolverFor("QF_LIA")
    solver.set(timeout=int(timeout*1000), random_seed=20261122)
    for row in b:
        for value in row:
            solver.add(value >= 1-size, value <= size-1)
    solver.add(z3.Or(*[z3.And(*[v != 0 for v in row]) for row in b]))
    for bits in itertools.product((0, 1), repeat=n):
        if not any(bits):
            continue
        values = [a+z3.Sum(*[v for v, bit in zip(row, bits) if bit])
                  for a, row in zip(poles, b)]
        solver.add(z3.Distinct(*values))
        solver.add(*[z3.And(value >= 1, value <= size) for value in values])
    # These linear identities follow from the vertex constraints, but help
    # the integer solver without introducing quadratic auxiliary equations.
    for i in range(n):
        solver.add(z3.Sum(*[row[i] for row in b]) == 0)
    result = solver.check()
    record = dict(n=n, size=size, status=str(result),
                  seconds=time.monotonic()-start,
                  required_row_support=n,
                  scope="Fixed arithmetic pole list and affine permutation cubes only.",
                  full_head_lower_bound=False)
    if result == z3.sat:
        model = solver.model()
        slopes = [[model.eval(v).as_long() for v in row] for row in b]
        record.update(poles=poles, slopes=slopes, audit=verify(n, poles, slopes))
    elif result == z3.unknown:
        record["reason_unknown"] = solver.reason_unknown()
    return record


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimensions", type=int, nargs="+", default=[3, 4, 5])
    parser.add_argument("--max-size", type=int, default=18)
    parser.add_argument("--seconds-per-instance", type=float, default=120)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    records = []
    for n in args.dimensions:
        for size in range(n+1, args.max_size+1):
            record = solve(n, size, args.seconds_per_instance)
            records.append(record)
            args.out.write_text(json.dumps(records, indent=2)+"\n")
            print(json.dumps({k:v for k,v in record.items()
                              if k not in ("poles", "slopes", "audit")}), flush=True)
            if record["status"] == "sat":
                break
