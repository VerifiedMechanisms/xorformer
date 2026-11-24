#!/usr/bin/env python3
"""Finite-field ranks of head-space variations modulo positive row scaling.

Nonzero minors give rigorous lower bounds over Q at the displayed integer
parameters, since all denominators and Gram determinants are nonzero mod p.
No upper bound or sign-complexity conclusion is inferred from this experiment.
"""
import json
from pathlib import Path
import numpy as np

P = 1000003
BASE = Path(__file__).resolve().parent

def rank(A):
    A = A.copy() % P
    r = 0
    for j in range(A.shape[1]):
        inds = np.flatnonzero(A[r:, j])
        if not len(inds):
            continue
        i = r+int(inds[0])
        A[[r, i]] = A[[i, r]]
        A[r] = A[r]*pow(int(A[r, j]), -1, P) % P
        A[r+1:] = (A[r+1:]-A[r+1:, j, None]*A[r, None, :]) % P
        r += 1
        if r == A.shape[0]:
            break
    return r

def inv(A):
    n = A.shape[0]
    C = np.concatenate([A.copy() % P, np.eye(n, dtype=np.int64)], axis=1)
    for j in range(n):
        inds = np.flatnonzero(C[j:, j])
        if not len(inds):
            raise ValueError('singular Gram matrix')
        i = j+int(inds[0])
        C[[j, i]] = C[[i, j]]
        C[j] = C[j]*pow(int(C[j, j]), -1, P) % P
        v = C[:, j].copy(); v[j] = 0
        C = (C-v[:, None]*C[j, None, :]) % P
    out = C[:, n:]
    assert np.array_equal(A@out % P, np.eye(n, dtype=np.int64))
    return out

records = []
for n in range(3, 7):
    for H in range(1, min(8, ((1 << n)-2)//n)+1):
        rng = np.random.default_rng(12000+100*n+H)
        bs = rng.integers(1, 101, size=(H, n), dtype=np.int64)
        N, r = 1 << n, n*H+1
        X = np.array([[(x >> i) & 1 for i in range(n)] for x in range(N)], dtype=np.int64)
        D = 1+X@bs.T
        DI = np.array([[pow(int(d), -1, P) for d in row] for row in D], dtype=np.int64)
        A = np.column_stack([np.ones(N, dtype=np.int64)]+
                            [X[:, i]*DI[:, h] % P for h in range(H) for i in range(n)])
        if rank(A) != r:
            records.append({'n': n, 'H': H, 'status': 'rank-deficient sample'})
            continue
        G = A.T@A % P
        K = (np.eye(N, dtype=np.int64)-(A@inv(G) % P)@A.T) % P
        assert not np.any(K@A % P)
        gauges = [(K[:, x, None]*A[x, None, :]) % P for x in range(N)]
        dirs = []
        for h in range(H):
            for j in range(n):
                dA = np.zeros((N, r), dtype=np.int64)
                for i in range(n):
                    dA[:, 1+n*h+i] = -X[:, i]*X[:, j]*(DI[:, h]**2 % P) % P
                dirs.append(K@dA % P)
        RG = np.column_stack([m.ravel() for m in gauges])
        RD = np.column_stack([m.ravel() for m in dirs])
        rg = rank(RG)
        total = rank(np.column_stack([RG, RD]))
        rec = {'n': n, 'H': H, 'field': P, 'rank': r, 'denominator_parameters': n*H,
               'row_gauge_rank': rg, 'joint_rank': total,
               'quotient_tangent_rank': total-rg, 'slopes': bs.tolist(),
               'status': 'exact modular rank', 'main_target_proved': False}
        records.append(rec)
        print(json.dumps({k:rec[k] for k in ['n','H','rank','row_gauge_rank','quotient_tangent_rank']}), flush=True)
(BASE/'quotient-tangent-ranks.json').write_text(json.dumps(records, indent=2)+'\n')
