"""Exact linear search on permutation branches, with realizable offsets.

Unlike a free-offset relaxation, every branch offset here is explicitly in the
span of residue and pole derivatives. SAT certificates can therefore be lifted
by the rational perturbation verifier. This is still not the attention model.
"""
import argparse
from fractions import Fraction as Q
import itertools
import json
from pathlib import Path
import time

import sympy as sp
import z3


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--queries',type=int,default=9)
    ap.add_argument('--locations',default='1,2,3,4')
    ap.add_argument('--poles',default='1,2,3,4,5,6,7,8,9')
    ap.add_argument('--seconds',type=float,default=7200)
    ap.add_argument('--seed',type=int,default=811729)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    p=list(map(sp.Rational,args.poles.split(',')))[:args.queries]
    t=list(map(sp.Rational,args.locations.split(',')))
    m,h=len(p),len(t)
    assert m==args.queries and 2<=h<=4 and all(v>0 for v in p+t)
    perms=list(itertools.permutations(range(h)))
    G=sp.Matrix([[-1/(v+pole)**2 for v in t] for pole in p])
    C=G*G[:h,:].inv()
    solver=z3.SolverFor('QF_LRA')
    solver.set(timeout=int(args.seconds*1000),random_seed=args.seed)
    offsets=[[None]*(m-h) for _ in perms]
    parameters=[]; ranks=[]
    for q in range(h,m):
        M=sp.Matrix([[1/(t[perm[i]]+p[q]) for i in range(h)] +
                    [-1/(t[perm[i]]+p[q])**2 for i in range(h)] +[-1]
                    for perm in perms])
        columns=M.rref()[1]; ranks.append(len(columns))
        variables=[z3.Real(f'a_{q}_{i}') for i in range(len(columns))]
        parameters.append(variables)
        for j in range(len(perms)):
            offsets[j][q-h]=z3.Sum([z3.RealVal(str(M[j,col]))*v
                                   for col,v in zip(columns,variables)])
    witnesses=[[z3.Real(f'v_{mask}_{i}') for i in range(h)] for mask in range(2**m)]
    branches=[[z3.Bool(f'b_{mask}_{j}') for j in range(len(perms))] for mask in range(2**m)]
    for mask in range(2**m):
        v=witnesses[mask]
        for q in range(h):
            solver.add((1 if (mask>>q)&1 else -1)*v[q]>=1)
        solver.add(z3.PbEq([(b,1) for b in branches[mask]],1))
        for j in range(len(perms)):
            for q in range(h,m):
                value=offsets[j][q-h]+z3.Sum([z3.RealVal(str(C[q,i]))*v[i] for i in range(h)])
                solver.add(z3.Implies(branches[mask][j],(1 if (mask>>q)&1 else -1)*value>=1))
    # Coordinate permutations act transitively on the permutation branches and
    # preserve the realizable-offset family. Fix one witness's branch.
    solver.add(branches[0][0])
    print(json.dumps({'started':True,'heads':h,'queries':m,'branches':len(perms),
                      'offset_ranks':ranks}),flush=True)
    start=time.monotonic();answer=solver.check()
    result={'solver_result':str(answer),'seconds':time.monotonic()-start,
            'scope':'LOCAL_LINEAR_MODEL_ONLY','poles':list(map(str,p)),
            'locations':list(map(str,t)),'permutations':perms,
            'gradient':[[str(x) for x in G.row(q)] for q in range(m)],
            'normalized_gradient':[[str(x) for x in C.row(q)] for q in range(m)],
            'offset_ranks':ranks}
    if answer==z3.sat:
        model=solver.model()
        def val(x):
            y=model.eval(x,model_completion=True)
            assert z3.is_rational_value(y)
            return Q(y.numerator_as_long(),y.denominator_as_long())
        e=[[val(x) for x in row] for row in offsets]
        v=[[val(x) for x in row] for row in witnesses]
        chosen=[next(j for j,b in enumerate(row) if z3.is_true(model.eval(b))) for row in branches]
        for mask in range(2**m):
            for q in range(m):
                z=sum(Q(str(C[q,i]))*v[mask][i] for i in range(h))
                if q>=h:z+=e[chosen[mask]][q-h]
                assert (1 if (mask>>q)&1 else -1)*z>=1
        result.update(offsets=[[str(x) for x in row] for row in e],
                      witnesses=[[str(x) for x in row] for row in v],
                      chosen_branches=chosen,exact_linear_verified=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k in
                     ['solver_result','seconds','scope','exact_linear_verified']}),flush=True)


if __name__=='__main__':main()
