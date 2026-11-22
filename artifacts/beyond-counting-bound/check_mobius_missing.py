"""Try exact rational-polynomial SMT on patterns missing from a finite search.

Only independently re-evaluated rational witnesses become certificates. Solver
UNSAT and UNKNOWN outcomes are diagnostics, not formalized impossibility claims.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time

import z3

from evolve_separable_mobius import verify


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--timeout-ms', type=int, default=60000)
    args = ap.parse_args()
    record = json.loads(args.source.read_text())
    p, r, c = (record[k] for k in ['poles', 'residuals', 'thresholds'])
    m, h = len(p), len(p[0])
    variables = z3.Reals(' '.join('theta'+str(i) for i in range(h)))
    polynomials = []
    for row in range(m):
        ds = [variables[i]+z3.RealVal(str(p[row][i])) for i in range(h)]
        polynomial = -z3.RealVal(str(c[row]))*z3.Product(ds)
        for i in range(h):
            polynomial += z3.RealVal(str(r[row][i]))*z3.Product([ds[j] for j in range(h) if i != j])
        polynomials.append(polynomial)
    diagnostics = []
    for mask in range(2**m):
        if str(mask) in record['witnesses']:
            continue
        solver = z3.SolverFor('QF_NRA')
        solver.set(timeout=args.timeout_ms)
        solver.add(*[v > 0 for v in variables])
        solver.add(*[(polynomial > 0 if (mask >> i) & 1 else polynomial < 0)
                     for i, polynomial in enumerate(polynomials)])
        start = time.monotonic()
        result = solver.check()
        diagnostic = dict(mask=mask, solver_result=str(result),
                          seconds=time.monotonic()-start,
                          scope='DIAGNOSTIC_ONLY')
        if result == z3.sat:
            model = solver.model()
            point = []
            for variable in variables:
                value = model.eval(variable, model_completion=True)
                if z3.is_rational_value(value):
                    rational = Fraction(value.numerator_as_long(),value.denominator_as_long())
                else:
                    approx = value.approx(100)
                    rational = Fraction(approx.numerator_as_long(),approx.denominator_as_long())
                point.append(str(rational))
            trial = dict(record)
            trial['witnesses'] = {str(mask):point}
            try:
                verify(trial)
            except AssertionError:
                diagnostic['rational_witness_verified'] = False
            else:
                record['witnesses'][str(mask)] = point
                diagnostic['rational_witness_verified'] = True
                diagnostic['scope'] = 'EXACT_RATIONAL_WITNESS'
        diagnostics.append(diagnostic)
        print(json.dumps(diagnostic),flush=True)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(dict(diagnostics=diagnostics,
                               source=str(args.source)),indent=2)+'\n')
    record['patterns'] = len(record['witnesses'])
    verify(record)
    args.output.with_suffix('.witnesses.json').write_text(json.dumps(record,indent=2)+'\n')


if __name__ == '__main__':
    main()
