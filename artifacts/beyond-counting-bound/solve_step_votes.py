"""Exact finite SAT search for threshold-vote shattering configurations.

The finite model uses every threshold gate on three Boolean inputs. Each of the
three coordinate comparisons is a chain across queries. SAT witnesses are
converted to rational reciprocal witnesses and checked independently. UNSAT is
only a solver diagnostic and concerns this finite step model, not all reciprocal
tests or the attention architecture.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

import z3

from evolve_separable_mobius import verify


def threshold_rules():
    cube = list(itertools.product([0, 1], repeat=3))
    rules = {}
    for w in itertools.product(range(-2, 3), repeat=3):
        values = [sum(a*b for a, b in zip(w, x)) for x in cube]
        for c2 in range(2*min(values)-1, 2*max(values)+2, 2):
            code = sum(int(2*v > c2) << j for j, v in enumerate(values))
            rules.setdefault(code, (w, c2))
    assert len(rules) == 104
    return cube, rules


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--queries', type=int, default=7)
    ap.add_argument('--seconds', type=float, default=7200)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seed', type=int, default=81379)
    args = ap.parse_args()
    m, h = args.queries, 3
    cube, rules = threshold_rules()
    solver = z3.SolverFor('QF_FD')
    solver.set(timeout=int(1000*args.seconds), random_seed=args.seed)
    table = [[z3.Bool(f't_{q}_{b}') for b in range(8)] for q in range(m)]
    s = [[[z3.Bool(f's_{mask}_{q}_{axis}') for axis in range(h)]
          for q in range(m)] for mask in range(2**m)]
    for q in range(m):
        # Relabeling a query complements its truth table. All output patterns
        # are required, so setting its all-zero entry to false loses nothing.
        solver.add(z3.Not(table[q][0]))
        for code in range(256):
            if code not in rules:
                solver.add(z3.Or(*[(z3.Not(table[q][b]) if (code >> b) & 1
                                    else table[q][b]) for b in range(8)]))
    for mask in range(2**m):
        for q in range(m):
            for b, pattern in enumerate(cube):
                literal = table[q][b] if (mask >> q) & 1 else z3.Not(table[q][b])
                solver.add(z3.Or(literal, *[
                    z3.Not(s[mask][q][axis]) if bit else s[mask][q][axis]
                    for axis, bit in enumerate(pattern)]))
        # Query permutation symmetry fixes the first coordinate's order.
        for q in range(m-1):
            solver.add(z3.Implies(s[mask][q][0], s[mask][q+1][0]))
    for axis in range(1, h):
        for a in range(m):
            for b in range(a+1, m):
                order = z3.Bool(f'order_{axis}_{a}_{b}')
                for mask in range(2**m):
                    solver.add(z3.Or(z3.Not(order), z3.Not(s[mask][a][axis]),
                                     s[mask][b][axis]))
                    solver.add(z3.Or(order, s[mask][a][axis],
                                     z3.Not(s[mask][b][axis])))
    started = time.monotonic()
    # QF_FD may internalize clauses and return an empty assertions() list.
    # Its length is therefore not a meaningful count of encoded constraints.
    print(json.dumps(dict(started=True, queries=m, solver='QF_FD')), flush=True)
    result = solver.check()
    diagnostic = dict(solver_result=str(result), queries=m,
                      elapsed_seconds=time.monotonic()-started,
                      scope='FINITE_STEP_MODEL_ONLY',
                      proof_status='SOLVER_DIAGNOSTIC')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.with_suffix('.diagnostic.json').write_text(
        json.dumps(diagnostic, indent=2)+'\n')
    print(json.dumps(diagnostic), flush=True)
    if result != z3.sat:
        return
    model = solver.model()
    bit = lambda x: int(z3.is_true(model.eval(x, model_completion=True)))
    values = [[[bit(v) for v in row] for row in witness] for witness in s]
    thresholds = [[0]*h for _ in range(m)]
    for axis in range(h):
        order = sorted(range(m), key=lambda q: sum(v[q][axis] for v in values))
        for rank, q in enumerate(order, 1):
            thresholds[q][axis] = rank
        for witness in values:
            chain = [witness[q][axis] for q in order]
            assert chain == sorted(chain)
    gates = [rules[sum(bit(v) << b for b, v in enumerate(row))] for row in table]
    base = 64*h+1
    poles = [[base**(2*t) for t in row] for row in thresholds]
    record = dict(poles=poles,
                  residuals=[[w*p for w, p in zip(gate[0], row)]
                             for gate, row in zip(gates, poles)],
                  thresholds=[str(c2)+'/2' for w, c2 in gates],
                  witnesses={str(mask):[base**(2*sum(1-v[q][axis] for q in range(m))+1)
                                         for axis in range(h)]
                             for mask, v in enumerate(values)},
                  step_thresholds=thresholds,
                  step_weights=[list(w) for w, c2 in gates],
                  step_twice_biases=[c2 for w, c2 in gates],
                  base=base, patterns=2**m, total_patterns=2**m,
                  status='EXACT_RATIONAL_WITNESSES')
    verify(record)
    args.output.write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps(dict(exact_rational_verified=True, patterns=2**m)), flush=True)


if __name__ == '__main__':
    main()
