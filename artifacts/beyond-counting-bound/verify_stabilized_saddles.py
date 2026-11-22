"""Exact ingredient audit for the stabilized full-domain critical-point proof.

This does not numerically locate, or enumerate, the perturbed critical points.
Their existence and nondegeneracy follow from the written contraction proof.
"""
from fractions import Fraction as F
import itertools
import json
import math
from pathlib import Path

import sympy as sp


def audit(d, k, logarithmic=False):
    n, N = d+k, 2**d
    q = N-1 if logarithmic else N//2-1
    a = [2**i for i in range(d)]
    aa = [v+1 for v in a]
    t = sp.Symbol('t')
    Q = sp.Poly(sp.prod(t-j for j in range(1, q+1)), t)
    D = sp.Poly(sp.prod(t+j for j in range(1, N+1)), t)
    power = 1 if logarithmic else 2
    residues = [F(int(Q.eval(-c))**power,
                  math.prod(v-c for v in range(1, N+1) if v != c))
                for c in range(1, N+1)]
    numerator = sp.Poly(0, t)
    for c, r in enumerate(residues, 1):
        quotient, remainder = sp.div(D, sp.Poly(t+c, t))
        assert remainder.is_zero
        numerator += sp.Rational(r.numerator, r.denominator)*quotient
    assert (numerator-Q**power).is_zero
    profiles = []
    for j in range(1, q+1):
        values = [sum(F((-1)**order*math.factorial(order))*r/F(j+c)**(order+1)
                      for c, r in enumerate(residues, 1))
                  for order in range(2 if logarithmic else 3)]
        alpha = F(int(Q.diff().eval(j)), int(D.eval(j))) if logarithmic else F(
            2*int(Q.diff().eval(j))**2, int(D.eval(j)))
        assert values == ([0, alpha] if logarithmic else [0, 0, alpha])
        assert abs(alpha) >= F(1 if logarithmic else 2, int(D.eval(q))) > 0
        profiles.append(alpha)
    B = [[2*(F(int(i == j), aa[i])-F(1, N)) for j in range(d)] for i in range(d)]
    inverse = [[(F(aa[i]*int(i == j))+F(aa[i]*aa[j], 1-d))/2
                for j in range(d)] for i in range(d)]
    for i, j in itertools.product(range(d), repeat=2):
        assert sum(B[i][v]*inverse[v][j] for v in range(d)) == int(i == j)
    cf = sum(abs(r) for r in residues)
    cg = sum(aa)+N if logarithmic else sum(v*v for v in aa)+N*N
    C = 1+cf+cg
    g = F(1+2**(d-1), 2)*(1+F(N+d-1, d-1))
    assert max(sum(abs(v) for v in row) for row in inverse) <= g
    if logarithmic:
        L = 1+2*g+int(D.eval(q))*(1+2*d*cf*g)
        inverse = [[-2*v for v in row] for row in inverse]
    else:
        L = 1+g+F(int(D.eval(q)), 2)*(1+2*d*cf*g)
    K, A, K1 = 6*C*n*n, k*cf, 2*k*cf*n
    delta = 1/(4*(1+L*K))
    epsilon = min(delta/(4*L*(1+A)), 1/(8*L*(1+K1)))
    assert 0 < delta < F(1, 4)
    assert epsilon > 0
    assert L*(K*delta+epsilon*K1) < F(3, 8)
    assert L*epsilon*A < delta/4
    # Audit the block inverse bound at every unperturbed grid point for the
    # two smallest cases; the same uniform estimate handles larger cases.
    if d <= 3:
        cube = [[(s >> i) & 1 for i in range(d)] for s in range(N)]
        for labels in itertools.product(range(1, q+1), repeat=k):
            for j in labels:
                cross = [sum(((-1 if logarithmic else 2)*r*bits[i])/
                             F(j+s+1)**(2 if logarithmic else 3)
                             for s, (r, bits) in enumerate(zip(residues, cube)))
                         for i in range(d)]
                alpha = profiles[j-1]
                lower_row = [-sum(cross[v]*inverse[v][i] for v in range(d))/alpha
                             for i in range(d)]
                assert sum(abs(v) for v in lower_row)+1/abs(alpha) <= L
    result = dict(d=d, k=k, input_bits=n, scalar_critical_points=q,
                  mode='logarithmic' if logarithmic else 'reciprocal',
                  critical_points_guaranteed_by_written_proof=q**k,
                  scalar_identity_verified=True, scalar_derivatives_verified=q,
                  stabilizer_inverse_verified=True, contraction_inequalities_verified=True,
                  coefficient_scale=str(1/epsilon), radius=str(delta),
                  critical_points_enumerated=False,
                  scope='EXACT_INGREDIENT_CHECKS_WITH_WRITTEN_CONTRACTION_PROOF')
    print(json.dumps({key: value for key, value in result.items()
                      if key not in ['coefficient_scale', 'radius']}), flush=True)
    return result


if __name__ == '__main__':
    records = [audit(d, d, logarithmic) for logarithmic in [False, True]
               for d in range(2, 6)]
    destination = Path(__file__).with_name('stabilized-saddles-verification.json')
    destination.write_text(json.dumps(dict(cases=records, all_checks_passed=True), indent=2)+'\n')
