#!/usr/bin/env python3
"""Exact finite checks for rectangular-shared-numerator-pair.tex."""
from fractions import Fraction as F
from itertools import product


def add(a, b):
    out = [F(0)] * max(len(a), len(b))
    for i, v in enumerate(a):
        out[i] += v
    for i, v in enumerate(b):
        out[i] += v
    return out


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, v in enumerate(a):
        for j, w in enumerate(b):
            out[i+j] += v*w
    return out


def ev(a, x):
    value = F(0)
    for v in reversed(a):
        value = value*x+v
    return value


def from_roots(roots):
    out = [F(1)]
    for x in roots:
        out = mul(out, [-x, F(1)])
    return out


def interp(points, values):
    out = [F(0)]
    for i, (x, value) in enumerate(zip(points, values)):
        basis = from_roots(points[:i] + points[i+1:])
        scale = value/ev(basis, x)
        out = add(out, [scale*v for v in basis])
    return out


def check_pair(q, sigma, tau):
    poles = [F(h+1, 100*q) for h in range(2*q)]
    queries = [F(1)+F(i, q) for i in range(q)]
    ps, pt = from_roots(poles[:q]), from_roots(poles[q:])
    p = mul(ps, pt)
    pd = [F(i)*p[i] for i in range(1, len(p))]
    # A rational one-parameter perturbation has at most finitely many bad
    # values. The distinct powers make every pole functional nonzero as
    # a polynomial in z; search only certifies these finite examples.
    for attempt in range(1, 200):
        z = F(1, 10+attempt)
        v = [F(sigma[i])+z**(i+1) for i in range(q)]
        w = [F(tau[i])+z**(q+i+1) for i in range(q)]
        a = interp(queries, [ev(pt, t)*(x+y)/2
                            for t, x, y in zip(queries, v, w)])
        b = interp(queries, [ev(ps, t)*(x-y)/2
                            for t, x, y in zip(queries, v, w)])
        aa, bb = mul(ps, a), mul(pt, b)
        n1 = add(aa, bb)
        n2 = add(aa, [-x for x in bb])
        c1 = [ev(n1, x)/ev(pd, x) for x in poles]
        c2 = [ev(n2, x)/ev(pd, x) for x in poles]
        if all(c1):
            break
    else:
        raise AssertionError("finite rational perturbation search failed")
    assert all(abs(x) == abs(y) for x, y in zip(c1, c2))
    assert c2[:q] == [-x for x in c1[:q]]
    assert c2[q:] == c1[q:]
    for i, t in enumerate(queries):
        f = sum((c/(t-x) for c, x in zip(c1, poles)), F(0))
        g = sum((c/(t-x) for c, x in zip(c2, poles)), F(0))
        assert f == v[i] == ev(n1, t)/ev(p, t)
        assert g == w[i] == ev(n2, t)/ev(p, t)
        assert sigma[i]*f > 0 and tau[i]*g > 0
    return q


def main():
    count = queries = 0
    for q in range(1, 5):
        words = list(product((-1, 1), repeat=q))
        for sigma in words:
            for tau in words:
                queries += check_pair(q, sigma, tau)
                count += 1
    print(f"PASS: {count} ordered word pairs; {2*queries} exact query scores")


if __name__ == "__main__":
    main()
