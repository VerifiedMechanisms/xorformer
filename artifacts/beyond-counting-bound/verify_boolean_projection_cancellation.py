#!/usr/bin/env python3
"""Finite exact checks for the independently written general proofs.

No numerical tolerance, asymptotic inference, or model change is used.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).parent


def compositions(k, n):
    if n == 1:
        yield (k,)
        return
    for a in range(k + 1):
        for tail in compositions(k - a, n - 1):
            yield (a,) + tail


def monomial_transfer(alpha):
    """Record each multiple of u_i^2 u_j - u_i u_j^2 exactly."""
    alpha = list(alpha)
    support = [i for i, a in enumerate(alpha) if a]
    if not support:
        return tuple(alpha), []
    j = max(support)
    steps = []
    for i in support[:-1]:
        while alpha[i] >= 2:
            old = tuple(alpha)
            multiplier = alpha[:]
            multiplier[i] -= 2
            multiplier[j] -= 1
            assert min(multiplier) >= 0
            alpha[i] -= 1
            alpha[j] += 1
            plus, minus = multiplier[:], multiplier[:]
            plus[i] += 2
            plus[j] += 1
            minus[i] += 1
            minus[j] += 2
            assert tuple(plus) == old and minus == alpha
            steps.append((i, j, tuple(multiplier)))
    assert all(alpha[i] == 1 for i in support[:-1])
    assert alpha[j] == sum(alpha) - len(support) + 1
    return tuple(alpha), steps


monomials = transfers = 0
hilbert_checks = []
for n in range(1, 7):
    for k in range(0, 9):
        normals = set()
        for alpha in compositions(k, n):
            normal, steps = monomial_transfer(alpha)
            normals.add(normal)
            assert sum(normal) == k
            assert [i for i, a in enumerate(normal) if a] == [i for i, a in enumerate(alpha) if a]
            monomials += 1
            transfers += len(steps)
        predicted = 1 if k == 0 else sum(comb(n, s) for s in range(1, min(k, n) + 1))
        assert len(normals) == predicted
        # The support-indicator evaluation matrix is triangular with diagonal one.
        if k:
            supports = sorted(({i for i, a in enumerate(v) if a} for v in normals),
                              key=lambda s: (len(s), sorted(s)))
            assert all(not a.issubset(b) for i, a in enumerate(supports)
                       for b in supports[:i])
        hilbert_checks.append((n, k, predicted))

vs = [(2, 1), (1, 2), (2, 0), (0, 2), (1, 0), (0, 1)]
cs = [1, -1, -1, 1, 1, -1]
reciprocal_checks = 0
for x, y in product((0, 1), repeat=2):
    groups = defaultdict(int)
    for (a, b), c in zip(vs, cs):
        groups[a*x+b*y] += c
    assert all(v == 0 for v in groups.values())
    for D in (F(1), F(7, 3), F(13)):
        for eps in (F(0), F(1, 11), F(1), F(19)):
            assert sum(F(c)/(D+eps*(a*x+b*y)) for (a, b), c in zip(vs, cs)) == 0
            reciprocal_checks += 1
assert sum(F(c)/(1+a*F(1, 2)+b*F(1, 3)) for (a, b), c in zip(vs, cs)) == F(-89, 5460)

moment_checks = []
for n in range(1, 9):
    for k in range(1, 13):
        m = n*k + 1
        weights = [(-1)**(m-h)*comb(m, h) for h in range(m+1)]
        assert all(sum(c*h**r for h, c in enumerate(weights)) == 0 for r in range(m))
        first = sum(c*h**(n*(k+1)) for h, c in enumerate(weights))
        assert first > 0
        # The first n+1 moment-curve points have a positive Vandermonde determinant.
        determinant = 1
        for i in range(n+1):
            for j in range(i+1, n+1):
                determinant *= j-i
        assert determinant > 0
        moment_checks.append({'n': n, 'k': k, 'heads': m+1,
                              'first_nonzero_moment': str(first),
                              'vandermonde_determinant': str(determinant)})

report = {'status': 'PASS', 'normal_form_monomials': monomials,
          'explicit_generator_transfers': transfers,
          'hilbert_dimension_checks': len(hilbert_checks),
          'six_term_reciprocal_checks': reciprocal_checks,
          'moment_curve_cases': len(moment_checks),
          'moment_curve_checks': moment_checks,
          'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'scope': 'Finite exact arithmetic checks; general theorems have separate written proofs.',
          'main_target_proved': False}
(BASE/'boolean-projection-rational-audit.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({k: v for k, v in report.items() if k != 'moment_curve_checks'}, indent=2))
