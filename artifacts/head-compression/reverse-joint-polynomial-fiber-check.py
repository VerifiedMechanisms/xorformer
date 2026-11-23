#!/usr/bin/env python3
"""Exact polynomial-fiber certificates. No asymptotic shattering claim."""
from collections import Counter
from fractions import Fraction as F
from itertools import permutations
from math import factorial, prod


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def poly_mul(p, q):
    r = [F(0)]*(len(p)+len(q)-1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i+j] += a*b
    return trim(r)


def root_poly(roots):
    out = [F(1)]
    for x in roots:
        out = poly_mul(out, [-x, F(1)])
    return out


def evaluate(p, x):
    out = F(0)
    for a in reversed(p):
        out = out*x+a
    return out


def divide(p, q):
    r = trim(p)
    out = [F(0)]*max(1, len(p)-len(q)+1)
    while len(r) >= len(q) and r != [0]:
        k = len(r)-len(q)
        c = r[-1]/q[-1]
        out[k] += c
        for j, a in enumerate(q):
            r[k+j] -= c*a
        r = trim(r)
    return trim(out), r


def inverse(a):
    n = len(a)
    m = [list(row)+[F(i == j) for j in range(n)] for i, row in enumerate(a)]
    for j in range(n):
        k = next(i for i in range(j, n) if m[i][j])
        m[j], m[k] = m[k], m[j]
        scale = m[j][j]
        m[j] = [x/scale for x in m[j]]
        for i in range(n):
            if i != j:
                scale = m[i][j]
                m[i] = [x-scale*y for x, y in zip(m[i], m[j])]
    return [row[n:] for row in m]


def q_coefficients(polynomials, tokens):
    degree = len(polynomials[0])-1
    return tuple(sum(polynomials[h][ell]*tokens[h]**(ell-1-k)
                     for h in range(len(tokens)) for ell in range(k+1, degree+1))
                 for k in range(degree))


checked = 0
for n in range(1, 6):
    lam = [F(j+1) for j in range(n)]
    d = [F(1000)-F(i+1, n+1) for i in range(n)]
    c = [[1/(x-y) for y in lam] for x in d]
    inv_c = inverse(c)
    p_lam, p_d = root_poly(lam), root_poly(d)
    v = [evaluate(p_d, lam[j])/prod(lam[j]-lam[k] for k in range(n) if k != j)
         for j in range(n)]
    for degree in range(1, 4):
        polynomials = [[F(((h+2)*(ell+3)+ell*ell) % 5-2)
                        for ell in range(degree+1)] for h in range(n)]
        e = [[evaluate(polynomials[h], d[i]) for h in range(n)] for i in range(n)]
        fibers = Counter()
        for p in permutations(range(n)):
            tokens = [lam[k] for k in p]
            q = q_coefficients(polynomials, tokens)
            fibers[q] += 1
            quotient, remainder = divide(poly_mul(q, p_lam), p_d)
            assert len(remainder) <= n
            for i in range(n):
                assert evaluate(remainder, d[i])/evaluate(p_lam, d[i]) == evaluate(q, d[i])
            ep = [sum(e[i][h]*c[i][p[h]] for h in range(n)) for i in range(n)]
            token_residues = [-sum(inv_c[j][i]*ep[i] for i in range(n)) for j in range(n)]
            a = [token_residues[p[h]] for h in range(n)]
            g = [v[j]*evaluate(quotient, lam[j]) for j in range(n)]
            expected = [-evaluate(polynomials[h], tokens[h])+g[p[h]] for h in range(n)]
            assert a == expected
            reduced = [-evaluate(polynomials[h], tokens[h]) for h in range(n)]
            for i in range(n):
                bias = sum(g[j]*c[i][j] for j in range(n))
                assert sum((e[i][h]+reduced[h])*c[i][p[h]] for h in range(n))+bias == 0
            assert abs(q[-1]) <= degree*2*n**degree
            assert q[-1] == sum(row[-1] for row in polynomials)
            assert all(abs(x) <= degree*2*n**degree and x.denominator == 1 for x in q)
            checked += 1
        bound = (2*degree*2*n**degree+1)**(degree-1)
        assert len(fibers) <= bound
        assert max(fibers.values())*bound >= factorial(n)

print(f"Verified {checked} exact polynomial residue formulas, corrected zeros, and fiber bounds.")
for n in (6, 7, 8):
    degree = 2
    polynomials = [[F(0), F(0), F(1 if h % 2 else -1)] for h in range(n)]
    fibers = Counter(q_coefficients(polynomials, p) for p in permutations(range(1, n+1)))
    print(f"H={n}, quadratic alternating profiles: {len(fibers)} fibers, largest={max(fibers.values())}, total={factorial(n)}")
