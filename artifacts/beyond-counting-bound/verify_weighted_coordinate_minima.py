#!/usr/bin/env python3
"""Exact finite audit. No positive-epsilon full-head certificate is claimed."""
from fractions import Fraction as F
from pathlib import Path
from math import prod
import hashlib
import json

BASE = Path(__file__).resolve().parent
m, k = 8, 3
roots = [F(1)+F(s, m) for s in range(1, m)]
eta = F(1, 36*k)


def P(t):
    return prod(t-r for r in roots)


def D(t):
    return prod(t+j for j in range(1, m+1))


lam = [P(F(-j))/prod(F(ell-j) for ell in range(1, m+1) if ell != j)
       for j in range(1, m+1)]


def quantities(t):
    R = P(t)/D(t)
    W = sum(1/(t+j)**2 for j in range(1, m+1))
    Wp = -2*sum(1/(t+j)**3 for j in range(1, m+1))
    Wpp = 6*sum(1/(t+j)**4 for j in range(1, m+1))
    a = sum(1/(t-r) for r in roots)
    b = sum(1/(t+j) for j in range(1, m+1))
    ellp = 2*(a-b)-Wp/W
    ellpp = (-2*sum(1/(t-r)**2 for r in roots)
             +2*sum(1/(t+j)**2 for j in range(1, m+1))
             -Wpp/W+(Wp/W)**2)
    return R, W, ellp, ellpp


def logW_second(t):
    W = sum(1/(t+j)**2 for j in range(1, m+1))
    Wp = -2*sum(1/(t+j)**3 for j in range(1, m+1))
    Wpp = 6*sum(1/(t+j)**4 for j in range(1, m+1))
    return Wpp/W-(Wp/W)**2


brackets = []
checks = 0
for s in range(1, m-1):
    lo, hi = roots[s-1]+F(1, 1024*m), roots[s]-F(1, 1024*m)
    assert quantities(lo)[2] > 0 > quantities(hi)[2]
    for _ in range(72):
        mid = (lo+hi)/2
        R, W, lp, lpp = quantities(mid)
        assert R == sum(c/(mid+j) for j, c in enumerate(lam, 1))
        assert lpp < -2*(m-2)
        assert sum(1/(mid+j)**2 for j in range(1, m+1)) < 1
        # Independent log-sum formula, including its nonnegative variance.
        terms = [prod((mid+ell)**2 for ell in range(1, m+1) if ell != j)
                 for j in range(1, m+1)]
        V = sum(terms)
        pi = [v/V for v in terms]
        gp = [2*sum(1/(mid+ell) for ell in range(1, m+1) if ell != j)
              for j in range(1, m+1)]
        gpp = [-2*sum(1/(mid+ell)**2 for ell in range(1, m+1) if ell != j)
               for j in range(1, m+1)]
        mean = sum(p*z for p, z in zip(pi, gp))
        variance = sum(p*(z-mean)**2 for p, z in zip(pi, gp))
        logVpp = sum(p*z for p, z in zip(pi, gpp))+variance
        assert logVpp == -2*sum(1/(mid+j)**2 for j in range(1, m+1))+logW_second(mid)
        assert lpp == -2*sum(1/(mid-r)**2 for r in roots)-logVpp
        checks += 1
        if lp > 0:
            lo = mid
        elif lp < 0:
            hi = mid
        else:
            raise AssertionError('Exact rational critical root: adapt the bracket audit.')
    assert quantities(lo)[2] > 0 > quantities(hi)[2]
    mid = (lo+hi)/2
    R, W, lp, lpp = quantities(mid)
    A = eta*R/W
    assert (A > 0) == (s % 2 == 1)
    assert abs(A) < F(1, 4*k)
    # At a critical point, the Hessian determinant is -2 W eta^2 phi''.
    # This rational probe verifies the completion of squares independently.
    for trialA in [F(-2), F(0), F(1, 7), A]:
        literal = sum((trialA/(mid+j)-eta*c)**2 for j, c in enumerate(lam, 1))
        completed = eta**2*sum(c*c for c in lam)-eta**2*R*R/W+W*(trialA-A)**2
        assert literal == completed
    brackets.append(dict(interval_index=s, lower=str(lo), upper=str(hi),
                         positive_amplitude=s % 2 == 1,
                         midpoint_approx=float(mid), amplitude_probe=str(A),
                         log_curvature_probe=str(lpp)))


def invert(M):
    n = len(M)
    A = [list(row)+[F(i == j) for j in range(n)] for i, row in enumerate(M)]
    det = F(1)
    for j in range(n):
        r = next(i for i in range(j, n) if A[i][j])
        if r != j:
            A[r], A[j] = A[j], A[r]
            det = -det
        pivot = A[j][j]
        det *= pivot
        A[j] = [x/pivot for x in A[j]]
        for i in range(n):
            if i != j:
                a = A[i][j]
                A[i] = [x-a*y for x, y in zip(A[i], A[j])]
    return [r[n:] for r in A], det


samples = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1),
           (1, 1, 0), (0, 1, 1), (1, 0, 1)]
J = []
for y in samples:
    den = F(1+sum((1 << j)*v for j, v in enumerate(y)))
    J.append([1/den]+[v/den for v in y]+[-v/den**2 for v in y])
Jinv, detJ = invert(J)
assert detJ == F(1, 1587600)
assert all(sum(Jinv[i][h]*J[h][j] for h in range(7)) == (i == j)
           for i in range(7) for j in range(7))

result = dict(status='PASS', arithmetic='exact fractions', m=m, k=k,
              partial_fraction_curvature_probes=checks,
              critical_root_brackets=brackets,
              positive_amplitude_brackets=sum(b['positive_amplitude'] for b in brackets),
              regression_square_checks=4*len(brackets),
              anchor_jacobian_det=str(detJ), anchor_inverse_entries_checked=49,
              written_full_head_minima_count=27,
              positive_epsilon_full_head_certificate='not computed; analytic existence is in the writeup',
              main_target_proved=False,
              script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(BASE/'weighted-coordinate-minima-rational-audit.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({key: value for key, value in result.items() if key != 'critical_root_brackets'}, indent=2))
