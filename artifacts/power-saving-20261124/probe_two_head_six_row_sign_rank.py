"""Search for a finite counterexample to same-width product compilation.

This is numerical discovery only. Any claimed certificate must subsequently
be checked using exact rational arithmetic on all entries and the original
positive-denominator compilation.
"""
import json
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(202611241)
base = Path(__file__).parent
known = json.loads((base / 'two_head_star_rational.json').read_text())

def exact_code(u, z, r, t, v, q, s, w):
    values = [(r[i]+s)/(u[i]+v)+(t[i]+w)/(z[i]+q) for i in range(6)]
    if any(y == 0 for y in values):
        return None
    return sum((1 << i) for i,y in enumerate(values) if y > 0)

best = 0
for trial in range(120):
    if trial < 40:
        rows = {k: list(map(int, known[k])) + [int(rng.integers(1,31) if k in ('u','z') else rng.integers(-40,41))]
                for k in ('u','z','r','t')}
    else:
        rows = {k: list(map(int, rng.integers(1,31,6) if k in ('u','z') else rng.integers(-40,41,6)))
                for k in ('u','z','r','t')}
    u,z,r,t = [np.array(rows[k],dtype=float) for k in ('u','z','r','t')]
    exact_rows = {k:list(map(Fraction,rows[k])) for k in rows}
    witnesses = {}
    # The two small denominator distances vary over several exact scales.
    samples = [(Fraction(int(rng.integers(1,31)),int(rng.integers(1,31))),
                Fraction(int(rng.integers(1,31)),int(rng.integers(1,31)))) for _ in range(60)]
    samples += [(Fraction(2)**int(rng.integers(-10,10)),Fraction(2)**int(rng.integers(-10,10)))
                for _ in range(120)]
    for dv,dq in samples:
        vf = dv-min(exact_rows['u']); qf = dq-min(exact_rows['z'])
        v=float(vf); q=float(qf)
        alpha=z+q; beta=u+v
        coeff=np.column_stack((alpha,beta))
        const=r*alpha+t*beta
        for rep in range(32):
            if rep in witnesses:
                continue
            for code in (rep,63-rep):
                signs=np.array([1 if code & (1<<i) else -1 for i in range(6)])
                result=linprog(np.zeros(2),A_ub=-signs[:,None]*coeff,
                    b_ub=signs*const-1,bounds=[(None,None),(None,None)],method='highs')
                if result.success:
                    sf,wf=[Fraction(float(y)).limit_denominator(10**7) for y in result.x]
                    got=exact_code(*(exact_rows[k] for k in ('u','z','r','t')),vf,qf,sf,wf)
                    if got==code:
                        witnesses[rep]={'code':code,'parameters':list(map(str,(vf,qf,sf,wf)))}
                        break
        if len(witnesses)>best:
            best=len(witnesses)
            print(json.dumps({'trial':trial,'best_antipodal_pairs':best}),flush=True)
        if len(witnesses)==32:
            payload={**rows,'witnesses':witnesses,'trial':trial}
            path=base/'two_head_six_row_sign_rank_candidate.json'
            path.write_text(json.dumps(payload,indent=2)+'\n')
            print(json.dumps({'found':str(path)}),flush=True)
            raise SystemExit(0)
    if trial%10==0:
        print(json.dumps({'trial_done':trial,'pairs':len(witnesses),'global_best':best}),flush=True)
print(json.dumps({'found':False,'global_best':best}),flush=True)
