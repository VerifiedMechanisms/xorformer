"""Find and exactly verify a dual obstruction for fixed endpoint denominators.

This rules out only these denominator choices, with arbitrary affine numerators.
It is not a lower bound on the number of vanilla heads. Run through heavy.
"""
import argparse
import json
import math
from pathlib import Path


def endpoint_denominators(p):
    ds = []
    for a, b, gamma, (v0, v1, vq) in zip(p['a'], p['b'], p['gamma'], p['values']):
        delta = v1 - v0
        if delta == 0:
            raise ValueError('A nondegenerate pure token-value difference is required')
        if delta * (vq - v0) > 0:
            slope = [abs(delta) * t for t in b]
            const = abs(vq - v0) * gamma
        else:
            slope = [-abs(delta) * t for t in a]
            const = abs(v1 - vq) * gamma - sum(slope)
        row = [2 * const + sum(slope)] + slope
        divisor = math.gcd(*row)
        ds.append([v // divisor for v in row])
    return ds


def features(n, ds, mask):
    z = [1] + [2 * ((mask >> i) & 1) - 1 for i in range(n)]
    values = [sum(a*b for a,b in zip(d,z)) for d in ds]
    return [value * math.prod(values[j] for j in range(len(ds)) if j != h)
            for h in range(len(ds)) for value in z]


def verify(record):
    n, ds = record['n'], record['denominators']
    assert ds and all(len(d) == n+1 and d[0] > sum(abs(v) for v in d[1:]) for d in ds)
    assert all(all(v>0 for v in d[1:]) or all(v<0 for v in d[1:]) for d in ds)
    truth = int(record['truth_table'],16)
    support, weights = record['vertices'], record['weights']
    assert len(support) == len(weights) and support and len(set(support)) == len(support)
    assert all(0 <= mask < (1 << n) for mask in support)
    assert all(isinstance(w,int) and w > 0 for w in weights)
    moments = [0] * ((n+1)*len(ds))
    for mask, w in zip(support,weights):
        sign = 1 if (truth >> mask) & 1 else -1
        for i,v in enumerate(features(n,ds,mask)):
            moments[i] += sign*w*v
    assert all(v==0 for v in moments), moments
    pure = record['pure_certificate']
    assert int(pure['truth_table'],16) == truth
    assert endpoint_denominators(pure) == ds
    assert all(v > 0 for row in pure['a'] + pure['b'] for v in row)
    assert all(v > 0 for v in pure['gamma'])
    cnum,cden = pure['constant']
    assert cden > 0
    for mask in range(1 << n):
        x=[(mask >> i)&1 for i in range(n)]
        d=[]; numerator=[]
        for a,b,gamma,(v0,v1,vq) in zip(pure['a'],pure['b'],pure['gamma'],pure['values']):
            d.append(gamma+sum(b[i] if x[i] else a[i] for i in range(n)))
            numerator.append(gamma*vq+sum(b[i]*v1 if x[i] else a[i]*v0 for i in range(n)))
        score=cnum*math.prod(d)+cden*sum(numerator[h]*math.prod(d[j] for j in range(len(d)) if j != h) for h in range(len(d)))
        sign=1 if (truth >> mask)&1 else -1
        assert sign*score > 0
    return len(weights)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('source')
    parser.add_argument('--sample',type=int,default=9)
    parser.add_argument('--verify',action='store_true')
    args=parser.parse_args()
    if args.verify:
        print('Verified exact fixed-denominator dual, support',verify(json.loads(Path(args.source).read_text())))
        return
    import numpy as np
    import sympy as sp
    from scipy.optimize import linprog
    source=next(json.loads(s) for s in Path(args.source).read_text().splitlines() if json.loads(s)['sample']==args.sample)
    n=source['n']; p=source['pure_certificate']; ds=endpoint_denominators(p)
    truth=int(p['truth_table'],16)
    rows=[features(n,ds,mask) for mask in range(1<<n)]
    signs=np.array([1 if (truth>>mask)&1 else -1 for mask in range(1<<n)],float)
    matrix=np.array(rows,float)
    matrix/=np.max(np.abs(matrix),axis=0)
    u,s,v=np.linalg.svd(matrix,full_matrices=False)
    rank=int(np.sum(s > 1e-12*s[0]))
    dualmatrix=signs[:,None]*u[:,:rank]
    result=linprog(np.zeros(1<<n),A_eq=np.vstack([dualmatrix.T,np.ones(1<<n)]),b_eq=np.r_[np.zeros(rank),1],bounds=(0,None),method='highs',options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
    print('Floating dual',result.success,'rank',rank,'singular values',s[-5:],flush=True)
    if not result.success:
        return
    support=[i for i,w in enumerate(result.x) if w>1e-9]
    exact=sp.Matrix([[int(signs[mask])*v for v in rows[mask]] for mask in support]).T
    kernel=exact.nullspace()
    print('Exact support',len(support),'kernel dimension',len(kernel),flush=True)
    if len(kernel)!=1:
        return
    vector=list(kernel[0]); sign=1 if vector[0]>0 else -1
    if not all(sign*v>0 for v in vector):
        print('Exact null vector is not positive; no certificate')
        return
    scale=sp.ilcm(*[v.q for v in vector])
    weights=[int(sign*scale*v) for v in vector]
    divisor=math.gcd(*weights); weights=[v//divisor for v in weights]
    record={'source':Path(args.source).name,'sample':args.sample,'n':n,'heads':len(ds),'denominators':ds,'truth_table':p['truth_table'],'vertices':support,'weights':weights,'pure_certificate':p,'scope':'Only fixed endpoint denominators are excluded, not other vanilla representations.'}
    verify(record)
    target=Path(__file__).parent/f'endpoint_dual_n{n}_sample{args.sample}.json'
    target.write_text(json.dumps(record,indent=2)+'\n')
    print('Exact certificate',target,'maximum weight digits',max(len(str(w)) for w in weights))


if __name__=='__main__':
    main()
