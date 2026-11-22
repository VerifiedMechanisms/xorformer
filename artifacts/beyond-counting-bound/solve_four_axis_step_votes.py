"""Search a finite four-axis threshold-vote relaxation, never a head lower bound.

Each query has an arbitrary four-bit linear threshold gate. Across queries,
each of the four comparison bits must form a chain. The 1882 threshold truth
tables are exhaustively enumerated using integer weights of magnitude at most
four. SAT produces witnesses independently checked by exact integer arithmetic.
UNSAT and timeout are diagnostics about this finite encoding only.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

import z3


def threshold_rules():
    cube=list(itertools.product([0,1],repeat=4))
    rules={}
    for w in itertools.product(range(-4,5),repeat=4):
        v=[sum(a*b for a,b in zip(w,x)) for x in cube]
        for c in range(2*min(v)-1,2*max(v)+2,2):
            code=sum(int(2*a>c)<<i for i,a in enumerate(v))
            rules.setdefault(code,(w,c))
    assert len(rules)==1882,len(rules)
    return cube,{code:data for code,data in rules.items() if not(code&1)}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--queries',type=int,default=9)
    ap.add_argument('--seconds',type=float,default=7200)
    ap.add_argument('--seed',type=int,default=117924)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();m=a.queries;h=4
    cube,rules=threshold_rules()
    solver=z3.SolverFor('QF_FD')
    solver.set(timeout=int(1000*a.seconds),random_seed=a.seed)
    table=[[z3.Bool(f't_{q}_{b}') for b in range(16)] for q in range(m)]
    comparisons=[[[z3.Bool(f's_{mask}_{q}_{i}') for i in range(h)]
                  for q in range(m)] for mask in range(2**m)]
    choices=[]
    for q in range(m):
        choice={code:z3.Bool(f'g_{q}_{code}') for code in rules}
        choices.append(choice)
        solver.add(z3.PbEq([(b,1) for b in choice.values()],1))
        for code,b in choice.items():
            for i in range(16):
                solver.add(z3.Implies(b,table[q][i] if (code>>i)&1 else z3.Not(table[q][i])))
    for mask in range(2**m):
        for q in range(m):
            for b,pattern in enumerate(cube):
                out=table[q][b] if (mask>>q)&1 else z3.Not(table[q][b])
                solver.add(z3.Or(out,*[z3.Not(comparisons[mask][q][i]) if bit
                                       else comparisons[mask][q][i]
                                       for i,bit in enumerate(pattern)]))
        for q in range(m-1):
            solver.add(z3.Implies(comparisons[mask][q][0],comparisons[mask][q+1][0]))
    for axis in range(1,h):
        for q in range(m):
            for r in range(q+1,m):
                order=z3.Bool(f'o_{axis}_{q}_{r}')
                for mask in range(2**m):
                    x,y=comparisons[mask][q][axis],comparisons[mask][r][axis]
                    solver.add(z3.Or(z3.Not(order),z3.Not(x),y))
                    solver.add(z3.Or(order,x,z3.Not(y)))
    print(json.dumps({'started':True,'heads':h,'queries':m,
                      'threshold_rules_up_to_complement':len(rules)}),flush=True)
    start=time.monotonic();answer=solver.check()
    result={'solver_result':str(answer),'elapsed_seconds':time.monotonic()-start,
            'queries':m,'heads':h,'scope':'FINITE_STEP_MODEL_ONLY',
            'proof_status':'SOLVER_DIAGNOSTIC'}
    if answer==z3.sat:
        model=solver.model()
        bit=lambda x:int(z3.is_true(model.eval(x,model_completion=True)))
        values=[[[bit(x) for x in row] for row in witness] for witness in comparisons]
        selected=[next(code for code,v in row.items() if bit(v)) for row in choices]
        gates=[rules[code] for code in selected]
        orders=[]
        for axis in range(h):
            order=sorted(range(m),key=lambda q:sum(v[q][axis] for v in values))
            orders.append(order)
            for witness in values:
                chain=[witness[q][axis] for q in order]
                assert chain==sorted(chain)
        for mask,witness in enumerate(values):
            for q,(w,c) in enumerate(gates):
                assert int(2*sum(x*y for x,y in zip(w,witness[q]))>c)==((mask>>q)&1)
        result.update(gates=gates,orders=orders,comparison_witnesses=values,
                      exact_finite_verified=True)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in
                     ['gates','orders','comparison_witnesses']}),flush=True)


if __name__=='__main__':main()
