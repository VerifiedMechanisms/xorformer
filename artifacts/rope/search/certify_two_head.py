"""Rationalize fits, then verify both architectures with Python integer arithmetic.

The verification routine uses no optimizer or floating-point arithmetic. A vanilla
certificate lists centered affine forms [constant, slopes...] for two positive
denominators and two numerators. Uniform nonzero denominator slopes and exact
cleared signs imply a two-head realization by the repository's normal-form theorem.
"""
import argparse
import itertools
import json
from pathlib import Path


def verify(record):
    n = record['n']
    p = record['pure_certificate']
    assert all(len(row) == n for row in p['a'] + p['b'])
    assert all(v > 0 for row in p['a'] + p['b'] for v in row)
    assert all(v > 0 for v in p['gamma'])
    cnum, cden = p['constant']
    assert cden > 0
    denominators = record['vanilla_integer_certificate']['denominators']
    numerators = record['vanilla_integer_certificate']['numerators']
    assert len(denominators) == len(numerators) == 2
    for d in denominators:
        assert len(d) == n+1 and d[0] > sum(abs(a) for a in d[1:])
        assert all(a > 0 for a in d[1:]) or all(a < 0 for a in d[1:])
    assert all(len(a) == n+1 for a in numerators)
    truth = int(p['truth_table'], 16)
    margin = None
    for j in range(1 << n):
        bits = [(j >> i) & 1 for i in range(n)]
        z = [1] + [2*x-1 for x in bits]
        pd, pn = [], []
        for h in range(2):
            v0, v1, vq = p['values'][h]
            pd.append(p['gamma'][h] + sum(p['b'][h][i] if bits[i] else p['a'][h][i] for i in range(n)))
            pn.append(p['gamma'][h]*vq + sum(p['b'][h][i]*v1 if bits[i] else p['a'][h][i]*v0 for i in range(n)))
        pure = cnum*pd[0]*pd[1] + cden*(pn[0]*pd[1]+pn[1]*pd[0])
        vd = [sum(a*b for a,b in zip(d,z)) for d in denominators]
        vn = [sum(a*b for a,b in zip(a,z)) for a in numerators]
        vanilla = vn[0]*vd[1] + vn[1]*vd[0]
        sign = 1 if (truth >> j) & 1 else -1
        assert sign*pure > 0 and min(vd) > 0 and sign*vanilla > 0, (record['sample'], j)
        margin = sign*vanilla if margin is None else min(margin,sign*vanilla)
    return margin


def rationalize(record):
    import numpy as np
    from scipy.optimize import linprog
    from search_two_head import vertices
    n=record['n']; Z=vertices(n); X=np.column_stack([np.ones(len(Z)),Z])
    truth=int(record['pure_certificate']['truth_table'],16)
    y=np.array([1 if (truth>>i)&1 else -1 for i in range(1<<n)])
    B=np.array(record['vanilla_search']['B'])
    for q in [10**6,10**9,10**12,10**15]:
        denominators=[]
        for b in B:
            slopes=[(1 if v>0 else -1)*max(1,round(abs(v)*q)) for v in b]
            gap=max(1,round((1-sum(abs(v) for v in b))*q))
            denominators.append([sum(abs(v) for v in slopes)+gap]+slopes)
        D = X@np.array(denominators,dtype=float).T/q
        F = np.column_stack([X*D[:,1,None],X*D[:,0,None]])
        lp=linprog(np.zeros(2*(n+1)),A_ub=-y[:,None]*F,b_ub=-np.ones(len(y)),bounds=[(None,None)]*(2*(n+1)),method='highs')
        if not lp.success: continue
        for r in [10**6,10**9,10**12,10**15]:
            numerators=[[int(round(a*r)) for a in row] for row in lp.x.reshape(2,n+1)]
            out={k:record[k] for k in ['sample','n','pure_certificate']}
            out['vanilla_integer_certificate']={'denominators':denominators,'numerators':numerators}
            try: out['minimum_integer_margin']=verify(out)
            except AssertionError: continue
            return out
    raise ValueError(f'No exact certificate for sample {record["sample"]}')


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('files',nargs='+'); ap.add_argument('--out'); args=ap.parse_args()
    if args.out:
        records={}
        for f in args.files:
            for line in Path(f).read_text().splitlines():
                a=json.loads(line); records[(a['n'],a['sample'])]=a
        exact=[rationalize(a) for a in records.values()]
        Path(args.out).write_text(''.join(json.dumps(a,separators=(',',':'))+'\n' for a in exact))
        print(f'EXACT CERTIFICATES: {len(exact)}; every cube input checked with integers.')
    else:
        total=0
        for f in args.files:
            for line in Path(f).read_text().splitlines(): verify(json.loads(line)); total+=1
        print(f'VERIFIED: {total} exact two-head certificates for both architectures.')

if __name__=='__main__': main()
