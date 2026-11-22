"""Search a rational gluing construction for ambiguous cube interpolation.

The two representations agree identically on x_5=0. On five selected points
of x_5=1, equality is linear in the numerators once denominators are fixed.
No numerical rank test is accepted as a certificate.
"""

import argparse
import json
from pathlib import Path
import numpy as np
import sympy as sp


def bits(j):
    return sp.Matrix([(j >> i) & 1 for i in range(5)])


def jacobian(u, b, indices):
    rows = []
    for j in indices:
        x = bits(j)
        den = [1 + bh.dot(x) for bh in b]
        num = [uh.dot(x) for uh in u]
        rows.append([x[i]/den[h] for h in range(2) for i in range(5)] +
                    [-num[h]*x[i]/den[h]**2 for h in range(2) for i in range(5)])
    return sp.Matrix(rows)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--trials', type=int, default=100)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--small-search', action='store_true')
    args = ap.parse_args()
    rng = np.random.default_rng(872903)
    best_height = None
    for trial in range(args.trials):
        bound = 4 if args.small_search else 10
        b = [sp.Matrix(rng.integers(1, bound, 5).tolist()) for _ in range(2)]
        beta = rng.integers(1, 3 if args.small_search else 8, 2).tolist()
        bq = [bh + sp.Matrix([0,0,0,0,be]) for bh, be in zip(b,beta)]
        upper = sorted(rng.choice(np.arange(16,32), 5, replace=False).tolist())
        indices = list(range(1,16)) + upper
        rows = []
        # Unknowns are u1[0:5], u2[0:5], alpha1, alpha2.
        for j in upper:
            x = bits(j)
            den = [1 + bh.dot(x) for bh in b]
            rows.append([beta[h]*x[i]/(den[h]*(den[h]+beta[h]))
                         for h in range(2) for i in range(5)] +
                        [-1/(den[h]+beta[h]) for h in range(2)])
        kernel = sp.Matrix(rows).nullspace()
        if not kernel:
            continue
        coeffs = rng.integers(-5,6,len(kernel)).tolist()
        v = sum((a*k for a,k in zip(coeffs,kernel)), sp.zeros(12,1))
        if args.small_search:
            v *= sp.ilcm(*[a.q for a in v])
            common = sp.igcd(*list(v))
            if common:
                v /= common
            height = max(abs(a) for a in v)
            if best_height is not None and height >= best_height:
                continue
        u = [v[0:5,0], v[5:10,0]]
        uq = [uh + sp.Matrix([0,0,0,0,v[10+h]]) for h,uh in enumerate(u)]
        jp, jq = jacobian(u,b,indices), jacobian(uq,bq,indices)
        ranks = [int(np.linalg.matrix_rank(np.array(j, dtype=float))) for j in (jp,jq)]
        if not args.small_search:
            print(json.dumps({'trial':trial,'ranks':ranks,'upper':upper}), flush=True)
        if min(ranks) != 20:
            continue
        determinants = [j.det(method='domain-ge') for j in (jp,jq)]
        if not all(determinants):
            continue
        data = {'indices':indices,
                'source':{'u':[[str(a) for a in h] for h in u],
                          'b':[[str(a) for a in h] for h in b]},
                'second':{'u':[[str(a) for a in h] for h in uq],
                          'b':[[str(a) for a in h] for h in bq]},
                'determinants':[str(d) for d in determinants]}
        args.output.write_text(json.dumps(data, indent=2)+'\n')
        if args.small_search:
            best_height = height
            print(json.dumps({'trial':trial,'height':int(height),'upper':upper}), flush=True)
        else:
            return


if __name__ == '__main__':
    main()
