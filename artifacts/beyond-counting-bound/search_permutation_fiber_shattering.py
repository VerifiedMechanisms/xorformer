"""Search local sign patterns near a symmetric positive Cauchy fiber.

This is a diagnostic search, not an attention-head lower-bound proof. With three
denominator parameters, six permutation branches have offsets whose alternating
sum is zero. First-order feasibility is linear after choosing a branch per sign
pattern. A SAT result is exported with exact rational coordinates; a separate
perturbation verifier must turn it into actual reciprocal witnesses.
"""
import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import time

import sympy as sp
import z3


def parity(p):
    return (-1)**sum(p[i] > p[j] for i in range(len(p))
                     for j in range(i+1, len(p)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--queries', type=int, default=7)
    ap.add_argument('--seconds', type=float, default=1800)
    ap.add_argument('--poles', type=str, default='1,2,3,4,5,6,7')
    ap.add_argument('--locations', type=str, default='1,2,3')
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seed', type=int, default=374813)
    args = ap.parse_args()
    m, h = args.queries, 3
    poles = list(map(sp.Rational, args.poles.split(',')))[:m]
    locations = list(map(sp.Rational, args.locations.split(',')))
    assert len(poles) == m and len(locations) == h
    assert all(x > 0 for x in poles+locations)
    permutations = list(itertools.permutations(range(h)))
    signs = list(map(parity, permutations))
    G = sp.Matrix([[-1/(t+p)**2 for t in locations] for p in poles])
    C = G * G[:h, :].inv()
    assert C[:h, :] == sp.eye(h)

    solver = z3.SolverFor('QF_LRA')
    solver.set(timeout=int(1000*args.seconds), random_seed=args.seed)
    offsets = [[z3.Real(f'e_{j}_{q}') for q in range(h,m)]
               for j in range(len(permutations))]
    for q in range(m-h):
        solver.add(z3.Sum([sgn*offsets[j][q]
                          for j, sgn in enumerate(signs)]) == 0)
    witnesses = [[z3.Real(f'v_{mask}_{j}') for j in range(h)]
                 for mask in range(2**m)]
    branches = [[z3.Bool(f'b_{mask}_{j}') for j in range(6)]
                for mask in range(2**m)]
    for mask in range(2**m):
        v = witnesses[mask]
        for q in range(h):
            solver.add((1 if (mask >> q) & 1 else -1)*v[q] >= 1)
        solver.add(z3.PbEq([(b, 1) for b in branches[mask]], 1))
        for j in range(6):
            for q in range(h,m):
                value = offsets[j][q-h] + z3.Sum([
                    z3.RealVal(str(C[q,i]))*v[i] for i in range(h)])
                solver.add(z3.Implies(branches[mask][j],
                    (1 if (mask >> q) & 1 else -1)*value >= 1))
    # Permute branches within each parity class without changing the model.
    # The all-negative labeling can be assigned to branch 0 or 1 depending on
    # its parity class. Complementing all offsets and witnesses exchanges the
    # two constant labelings, but is not used as an extra symmetry assumption.
    solver.add(z3.Or(branches[0][0], branches[0][1]))
    print(json.dumps({'started':True,'queries':m,'permutation_branches':6,
                      'poles':list(map(str,poles))}), flush=True)
    start=time.monotonic(); answer=solver.check()
    result={'solver_result':str(answer),'seconds':time.monotonic()-start,
            'scope':'LOCAL_LINEAR_MODEL_ONLY','poles':list(map(str,poles)),
            'locations':list(map(str,locations)),
            'permutations':permutations,'parities':signs,
            'gradient':[[str(x) for x in G.row(i)] for i in range(m)],
            'normalized_gradient':[[str(x) for x in C.row(i)] for i in range(m)]}
    if answer == z3.sat:
        model=solver.model()
        def rational(x):
            v=model.eval(x,model_completion=True)
            assert z3.is_rational_value(v)
            return Fraction(v.numerator_as_long(),v.denominator_as_long())
        e=[[rational(x) for x in row] for row in offsets]
        v=[[rational(x) for x in row] for row in witnesses]
        chosen=[next(j for j,b in enumerate(row)
                     if z3.is_true(model.eval(b))) for row in branches]
        for q in range(m-h):
            assert sum(signs[j]*e[j][q] for j in range(6)) == 0
        for mask in range(2**m):
            for q in range(m):
                value=sum(Fraction(str(C[q,i]))*v[mask][i] for i in range(h))
                if q >= h: value += e[chosen[mask]][q-h]
                assert (1 if (mask >> q)&1 else -1)*value >= 1
        result.update(offsets=[[str(x) for x in row] for row in e],
                      witnesses=[[str(x) for x in row] for row in v],
                      chosen_branches=chosen, exact_linear_verified=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k in
          ['solver_result','seconds','scope','exact_linear_verified']}),flush=True)


if __name__ == '__main__':
    main()
