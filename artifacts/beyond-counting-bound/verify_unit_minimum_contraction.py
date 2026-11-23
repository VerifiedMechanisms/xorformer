"""Exact integer audit of a full-cube unit-margin strict local minimum.

The data consist of rational approximations, not asserted exact roots. The
inequalities verified here imply a root by the contraction mapping theorem.
The analytic implication and all conservative constants are documented in the
accompanying writeup. No floating arithmetic is used in any assertion.
"""
import argparse
import hashlib
import json
import time
from fractions import Fraction
from pathlib import Path


def nearest(num, den):
    assert den > 0
    q = (2*num+den)//(2*den)
    assert 2*abs(num-q*den) <= den
    return q


def sums(a):
    out = [0]*(1 << len(a))
    for i, value in enumerate(a):
        size = 1 << i
        out[size:2*size] = [v+value for v in out[:size]]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('data', type=Path)
    ap.add_argument('output', type=Path)
    args = ap.parse_args()
    start = time.monotonic()
    d = json.loads(args.data.read_text())
    n, h = d['n'], d['heads']
    q, m = n*h, 2*n*h
    assert (n, h) == (18, 3)
    D = int(d['denominator'])
    assert D == 10**70
    z = list(map(int, d['center']))
    R = [list(map(int, row)) for row in d['inverse']]
    lam = list(map(int, d['dual']))
    active = d['active_vertices']
    ys = d['active_labels']
    gamma = Fraction(d['gamma'])
    assert len(z) == m and len(R) == m and all(len(row) == m for row in R)
    assert len(lam) == m and len(ys) == m
    assert len(active) == m and len(set(active)) == m and 0 not in active
    assert all(0 < v < (1 << n) for v in active)
    assert all(y in (-1, 1) for y in ys) and gamma > 0
    assert all(-D < v < 0 for v in z[q:])
    assert all(1000*v < -D for v in z[q:])
    assert max(map(abs,z[:q])) < D//2
    assert all(100*(D+sum(z[q+i*h+j] for i in range(n))) > D for j in range(h))
    assert max(sum(abs(v) for v in row) for row in R) < 100000*D
    assert min(lam)*1000 > 3*D and max(lam) < 1000000*D

    # Each Jacobian entry is rounded to the same denominator D. The exact
    # rounding error is at most 1/(2D), as checked by nearest().
    J = []
    max_residual = Fraction(0)
    for vertex, y in zip(active, ys):
        bits = [i for i in range(n) if (vertex >> i) & 1]
        aa = [sum(z[i*h+j] for i in bits) for j in range(h)]
        bb = [D+sum(z[q+i*h+j] for i in bits) for j in range(h)]
        value = sum((Fraction(a,b) for a,b in zip(aa,bb)), Fraction(0))
        residual = abs(value + (gamma if y < 0 else 0))
        assert residual < Fraction(1,10**60)
        max_residual = max(max_residual,residual)
        row = [0]*m
        for i in bits:
            for j in range(h):
                row[i*h+j] = nearest(D*D,bb[j])
                row[q+i*h+j] = nearest(-aa[j]*D*D,bb[j]*bb[j])
        J.append(row)
    # The exact norm bound ||I-R J(center)||_infinity < 10^-50 follows by
    # adding m*||R||/(2D) to the checked rounded-matrix product.
    JT = list(zip(*J))
    inverse_error_numerator = max(sum(abs((D*D if i == j else 0)-sum(a*b for a,b in zip(row,col)))
                                           for j,col in enumerate(JT)) for i,row in enumerate(R))
    inverse_error = Fraction(inverse_error_numerator,D*D) + Fraction(m*100000,2*D)
    assert inverse_error < Fraction(1,10**50)
    signed_lam = [y*v for y,v in zip(ys,lam)]
    dual_residual_numerator = max(abs(sum(a*b for a,b in zip(col,signed_lam)) -
                                      (D*z[j] if j < q else 0)) for j,col in enumerate(JT))
    dual_error = Fraction(dual_residual_numerator,D*D) + Fraction(m*1000000,2*D)
    assert dual_error < Fraction(1,10**50)
    print(json.dumps(dict(status='ACTIVE_AND_INVERSE_INTEGER_CHECKS_PASS')),flush=True)

    aa = [sums([z[i*h+j] for i in range(n)]) for j in range(h)]
    bb = [[D+v for v in sums([z[q+i*h+j] for i in range(n)])] for j in range(h)]
    selected = set(active)
    positives = negatives = 0
    gap_den = 10**8
    for v in range(1,1 << n):
        if v in selected:
            continue
        b0,b1,b2 = (a[v] for a in bb)
        Q = b0*b1*b2
        P = aa[0][v]*b1*b2 + aa[1][v]*b0*b2 + aa[2][v]*b0*b1
        if gap_den*P >= Q:
            positives += 1
        else:
            assert gap_den*(gamma.denominator*P+gamma.numerator*Q) <= -gamma.denominator*Q, v
            negatives += 1
    assert positives+negatives+m+1 == (1 << n)

    # Analytic constants on the radius-r infinity ball: B >= beta, |u| <= 1;
    # every entry of J is L-Lipschitz; every cube score is K-Lipschitz.
    r = Fraction(1,10**40)
    beta = Fraction(1,1000)
    L = 10**12
    K = 10**10
    assert Fraction(1,100)-n*r > beta
    assert r < Fraction(1,1000)
    assert Fraction(1,2)+r < 1
    assert n/beta**2+2*n*n/beta**3 < L
    assert n*h/beta+n*n*h/beta**2 < K
    contraction = inverse_error + 100000*m*L*r
    displacement = 100000*max_residual
    assert contraction < Fraction(1,2)
    assert displacement < r/2
    assert K*r < Fraction(1,2*gap_den)
    # At the root, the inverse transpose norm is at most m*Rnorm/(1-q).
    inverse_transpose_bound = Fraction(m*100000,1-contraction)
    dual_change = inverse_transpose_bound*(r + dual_error + m*L*r*1000000)
    assert dual_change < Fraction(1,1000)
    result = dict(status='EXACT_CONTRACTION_CERTIFICATE_PASS',
                  data_sha256=hashlib.sha256(args.data.read_bytes()).hexdigest(),
                  verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  n=n,heads=h,parameter_count=m,vertices_checked=1 << n,
                  selected_active_count=m,unselected_positive_count=positives,
                  unselected_negative_count=negatives,
                  rational_bounds=dict(radius=str(r),denominator_lower_bound=str(beta),
                    jacobian_entry_lipschitz=L,score_lipschitz=K,
                    inverse_norm_upper_bound=100000,inverse_error=str(inverse_error),
                    active_residual=str(max_residual),dual_residual=str(dual_error),
                    contraction=str(contraction),dual_change=str(dual_change),
                    unselected_margin_gap='1/100000000',root_multiplier_lower_bound='1/500'),
                  exact_integer_assertions=True,lean_checked=False,
                  implication='Existence and strict local minimality require the written analytic argument.',
                  main_target_proved=False,elapsed_seconds=time.monotonic()-start)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('rational_bounds',)}),flush=True)


if __name__ == '__main__':
    main()
