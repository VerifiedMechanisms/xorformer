#!/usr/bin/env python3
"""Exact small-instance checks, not a numerical proof of generic balancing."""
from fractions import Fraction as F
from itertools import product, combinations
from math import prod
from pathlib import Path
import hashlib
import json
import sympy as sp

BASE = Path(__file__).resolve().parent
cases = []
for n, bs in [(2, [(2, 3)]), (3, [(2, 3, 5)]),
              (3, [(1, 2, 3), (4, 5, 8)])]:
    X = list(product((0, 1), repeat=n))
    N = len(X)
    den = [[1+sum(bi*xi for bi, xi in zip(b, x)) for b in bs] for x in X]
    A = sp.Matrix([[1]+[sp.Rational(xi, D) for D in ds for xi in x]
                   for x, ds in zip(X, den)])
    r = A.cols
    assert A.rank() == r
    basis_sets = []
    for B in combinations(range(N), r):
        if A[list(B), :].det() != 0:
            basis_sets.append(frozenset(B))
    basis_family = set(basis_sets)
    index = {x: i for i, x in enumerate(X)}
    for v in X:
        perm = [index[tuple(xi ^ vi for xi, vi in zip(x, v))] for x in X]
        assert all(frozenset(perm[i] for i in B) in basis_family for B in basis_sets)
    multiplicities = [sum(i in B for B in basis_sets) for i in range(N)]
    assert all(F(k, len(basis_sets)) == F(r, N) for k in multiplicities)
    # For these instances, multiplying the denominators gives the fixed
    # multilinear space of degree at most H. This is checked, not assumed.
    s = [prod(ds) for ds in den]
    C = sp.diag(*s)*A
    P = C*(C.T*C).inv()*C.T
    assert P*P == P and P.T == P
    assert all(P[i, i] == sp.Rational(r, N) for i in range(N))
    assert P*C == C
    cases.append({'n': n, 'H': len(bs), 'rank': r, 'basis_count': len(basis_sets),
                  'basis_memberships': multiplicities,
                  'positive_scaling': s, 'projection_diagonal': str(F(r, N))})

spike_cases = []
for n in range(5, 10):
    a = list(range(1, n+1))
    # Leading coefficients agree, so the polynomial quotient is exactly one.
    residues = [F(prod(-h-j for j in range(1, n+1)),
                  prod(ell-h for ell in a if ell != h)) for h in a]
    table = []
    for x in product((0, 1), repeat=n):
        t = sum(x)
        rhs = F(1)+sum(c/F(t+h) for h, c in zip(a, residues))
        lhs = F(prod(t-j for j in range(1, n+1)), prod(t+h for h in a))
        assert rhs == lhs
        assert (rhs != 0) == (t == 0)
        table.append(rhs)
    assert 1+n*n < 2**n
    spike_cases.append({'n': n, 'origin_value': str(table[0]),
                        'checked_cube_values': len(table),
                        'residues': list(map(str, residues))})

balanced_lines = 0
N = 8
for y in product((-1, 1), repeat=N):
    P = [[F(yi*yj, N) for yj in y] for yi in y]
    for i in range(N):
        assert P[i][i] == F(1, N)
        assert sum(P[i][j]*y[j] for j in range(N)) == y[i]
        for j in range(N):
            assert sum(P[i][k]*P[k][j] for k in range(N)) == P[i][j]
    balanced_lines += 1

result = {'status': 'PASS', 'exact_head_space_examples': cases,
          'nonbalanceable_special_denominator_examples': spike_cases,
          'balanced_sign_lines': balanced_lines,
          'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'scope': 'Exact finite examples. General generic balancing is proved in the written note; no asymptotic head lower bound.',
          'main_target_proved': False}
(BASE/'symmetric-row-balancing-rational-audit.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'status': 'PASS', 'head_space_examples': len(cases),
                  'spike_examples': len(spike_cases), 'balanced_sign_lines': balanced_lines}))
