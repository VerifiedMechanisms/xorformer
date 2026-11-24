#!/usr/bin/env python3
"""Exact rational audit of the written three-head/eight-column theorem.

This checks every one of the 256 patterns and their leading coefficients,
then embeds tables of several sizes in strict reverse full-cube heads.
It supplements the written universal proof; it is not a Lean proof.
"""

from fractions import Fraction as F
from itertools import product


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def inverse(a):
    n = len(a)
    aug = [list(row)+[F(i == j) for j in range(n)]
           for i, row in enumerate(a)]
    det = F(1)
    for j in range(n):
        k = next(k for k in range(j, n) if aug[k][j])
        if j != k:
            aug[j], aug[k] = aug[k], aug[j]
            det = -det
        pivot = aug[j][j]
        det *= pivot
        aug[j] = [x/pivot for x in aug[j]]
        for k in range(n):
            if k != j:
                coeff = aug[k][j]
                aug[k] = [x-coeff*y for x, y in zip(aug[k], aug[j])]
    return [row[n:] for row in aug], det


def poly_mul(p, q):
    out = [F(0)]*(len(p)+len(q)-1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i+j] += x*y
    return out


T = F(101, 100)
A0 = [F(1), F(1), F(-2)]
WA = [F(1), F(1), F(1)]
WB = [F(101, 100), F(99, 100), F(1)]
W = [[F(101, 100), F(24, 25), F(1)],
     [F(51, 50), F(26, 25), F(49, 50)],
     [F(1), F(51, 50), F(101, 100)],
     [F(1), F(99, 100), F(1)]]
V = [[F(10), F(-8), F(-475, 303)],
     [F(-5), F(-10), F(18865, 1326)],
     [F(7), F(7), F(-71407, 5100)],
     [F(0), F(-2), F(200, 99)]]
L = [[dot(A0, w)]+v for w, v in zip(W, V)]
INV, DET = inverse(L)
assert DET == F(835605281, 736593000)
assert all(dot(v, [1/x for x in w]) == 0 for w, v in zip(W, V))

QUERIES = []
for w in (WA, WB):
    for scale in (F(1), T):
        QUERIES.append(([scale/x for x in w], [F(0)]*3))
for w, v in zip(W, V):
    QUERIES.append(([1/x for x in w], [v[h]/w[h]**2 for h in range(3)]))
assert all(F(25, 26) <= d <= F(25, 24)
           for ds, _ in QUERIES for d in ds)

U = INV[0]
VA = [INV[1][j]+INV[2][j]-2*INV[3][j] for j in range(4)]
VB = [T**2*INV[1][j]+F(99, 100)**2*INV[2][j]-2*INV[3][j]
      for j in range(4)]
EXPECTED_ROWS = [
    [F(3643867900, 358116549), F(371958600, 119372183),
     F(-30859300000, 2506815843), F(-11861500200, 119372183)],
    [F(72215, 238744366), F(-86658, 596860915),
     F(118924450, 835605281), F(-563277, 238744366)],
    [F(2906209249, 1432466196000), F(1868678071, 2984304575000),
     F(71834075071, 501363168600), F(418378323, 2387443660000)]]
assert [U, VA, VB] == EXPECTED_ROWS
for v in (U, VA, VB):
    for j in range(4):
        assert sum(abs(x) for k, x in enumerate(v) if k != j) < 1000*abs(v[j])
SIGN_PAIRS = [(1, 1), (-1, 1), (-1, -1), (1, -1)]
assert all(sa*U[j]*VA[j] > 0 and sb*U[j]*VB[j] > 0
           for j, (sa, sb) in enumerate(SIGN_PAIRS))


def direction(signs):
    j = SIGN_PAIRS.index((signs[0], signs[2]))
    y = [F(s*(1000 if k == j else 1)) for k, s in enumerate(signs[4:])]
    lam, *p = [dot(row, y) for row in INV]
    qa = lam*dot(A0, p)
    qb = lam*dot([a*w*w for a, w in zip(A0, WB)], p)
    assert signs[0]*qa > 0 and signs[2]*qb > 0
    la = F(0) if signs[0] == signs[1] else -qa*(T+1)/(2*T)
    lb = F(0) if signs[2] == signs[3] else -qb*(T+1)/(2*T)
    a2 = [50*(lb-la), -50*(lb-la), la]
    assert dot(WA, a2) == la and dot(WB, a2) == lb
    leading_scores = [la+qa, (T*la+qa)/T**2,
                      lb+qb, (T*lb+qb)/T**2]+y
    bounds = [F(1, 2)]
    for j, ((ds, bs), expected) in enumerate(zip(QUERIES, leading_scores)):
        cleared = [F(0)]*5
        for h in range(3):
            term = [bs[h], lam*A0[h], a2[h]]
            for g in range(3):
                if g != h:
                    term = poly_mul(term, [ds[g], -p[g]])
            cleared = [x+y for x, y in zip(cleared, term)]
        k = 2 if j < 4 else 1
        assert all(x == 0 for x in cleared[:k])
        assert cleared[k] == expected*ds[0]*ds[1]*ds[2]
        assert signs[j]*cleared[k] > 0
        tail = sum(abs(x) for x in cleared[k+1:])
        if tail:
            bounds.append(abs(cleared[k])/(2*tail))
        bounds += [d/(2*abs(x)) for d, x in zip(ds, p) if x]
    return lam, p, a2, min(bounds)


SIGNS = list(product((-1, 1), repeat=8))
DIRECTIONS = [direction(s) for s in SIGNS]
MAX_P = max(abs(x) for _, p, _, _ in DIRECTIONS for x in p)
SIGN_BOUND = min(bound for _, _, _, bound in DIRECTIONS)


def check_table(r):
    rho = F(1, 1000*r)
    d0 = F(19, 20)
    bound = min(SIGN_BOUND, rho/(2*d0*MAX_P))
    delta = F(1, 2)
    while delta >= bound:
        delta /= 2
    rows = [DIRECTIONS[i % 256] for i in range(r)]
    pp = [[rho+d0*delta*row[1][h] for row in rows] for h in range(3)]
    qq = [[1-rho-d0*ds[h] for ds, _ in QUERIES] for h in range(3)]
    aa = [[d0*(delta*lam*A0[h]+delta**2*a2[h])
           for lam, _, a2, _ in rows] for h in range(3)]
    bb = [[d0*bs[h] for _, bs in QUERIES] for h in range(3)]
    for h in range(3):
        assert all(rho/2 < x < 3*rho/2 for x in pp[h])
        assert all(0 < F(1, 96)-rho <= x < F(9, 104) for x in qq[h])
        assert sum(pp[h])+sum(qq[h]) < F(3, 2000)+F(9, 13) < 1
    for i in range(r):
        for j, (ds, bs) in enumerate(QUERIES):
            actual = sum((aa[h][i]+bb[h][j])/(1-pp[h][i]-qq[h][j])
                         for h in range(3))
            lam, p, a2, _ = rows[i]
            normalized = sum((delta*lam*A0[h]+delta**2*a2[h]+bs[h]) /
                             (ds[h]-delta*p[h]) for h in range(3))
            assert actual == normalized
            assert SIGNS[i % 256][j]*actual > 0
    if r <= 2:
        for z in product((0, 1), repeat=r):
            for w in product((0, 1), repeat=8):
                assert all(1-dot(pp[h], z)-dot(qq[h], w) > 0 for h in range(3))
    return r*8


def main():
    total = sum(check_table(r) for r in (1, 2, 7, 256, 513))
    print("Exact germ audit passed all 256 patterns and all leading coefficients.")
    print(f"Full-cube embeddings passed {total} grid signs, with every slope strict.")
    print("This is a fixed three-head/eight-query theorem, not an asymptotic saving.")


if __name__ == '__main__':
    main()
