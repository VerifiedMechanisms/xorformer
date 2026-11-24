#!/usr/bin/env python3
"""Exact checks for the written compact H=2, five-query construction.

No floating-point solver is used. These checks supplement the uniform
inequalities proved in reverse-unbalanced-h2-local.tex; they do not replace
that proof or constitute a Lean formalization.
"""

from fractions import Fraction as F
from itertools import product


def query_data(eps):
    t = 1 + eps
    return [
        ((F(1), F(1)), (F(0), F(0))),
        ((t, t), (F(0), F(0))),
        ((1-eps, F(1)), (eps*(1-eps), -eps)),
        ((1-eps, F(1)), (-eps*(1-eps), eps)),
        ((1-2*eps, F(1)), (4*eps*(1-2*eps), -4*eps)),
    ]


def witness(signs, eps, delta):
    t = 1 + eps
    if signs[0] == 1:
        y1, y2, y3 = 8*signs[2], signs[3], signs[4]
    else:
        y1, y2, y3 = signs[2], 8*signs[3], signs[4]
    x = F(y1+y2, 2)
    v = F(5*y1-3*y2-2*y3, 4)
    p = F(2*y3-3*y1+y2, 4)/eps
    q = x*v
    lam = F(0) if signs[0] == signs[1] else -q*(t+1)/(2*t)
    assert signs[0]*q > 0
    assert (x+v+eps*p, x-v-eps*p, x+2*v+4*eps*p) == (y1,y2,y3)
    assert abs(x) <= 5 and abs(v) <= 12
    assert abs(p) <= 7/eps and abs(p+v) <= 8/eps
    assert 0 < abs(q) <= 60 and abs(lam) <= abs(q)
    slopes = (delta*(p+v), delta*p)
    nums = (delta*x, -delta*x+delta**2*lam)
    for j, ((d1,d2),(b1,b2)) in enumerate(query_data(eps)):
        p1,p2 = slopes
        a1,a2 = nums
        cleared = (a1+b1)*(d2-p2)+(a2+b2)*(d1-p1)
        if j < 2:
            expected = delta**2*((1 if j == 0 else t)*lam+q)-delta**3*lam*(p+v)
        else:
            k = eps if j < 4 else 2*eps
            expected = delta*k*(y1,y2,y3)[j-2]+delta**2*((1-k)*lam+q)-delta**3*lam*(p+v)
        assert cleared == expected
        assert d1 > p1 and d2 > p2
        assert signs[j]*cleared > 0
    return slopes, nums


def check_table(r, eps):
    rho = eps/(100*r)
    delta = rho*eps**2/100
    d0 = 1-10*eps
    signs_list = list(product((-1,1), repeat=5))
    rows = [signs_list[i % 32] for i in range(r)]
    witnesses = [witness(s,eps,delta) for s in rows]
    q = [[1-rho-d0*query_data(eps)[j][0][h] for j in range(5)] for h in range(2)]
    p = [[rho+d0*witnesses[i][0][h] for i in range(r)] for h in range(2)]
    a = [[d0*witnesses[i][1][h] for i in range(r)] for h in range(2)]
    b = [[d0*query_data(eps)[j][1][h] for j in range(5)] for h in range(2)]
    for h in range(2):
        assert all(rho/2 < v < 2*rho for v in p[h])
        assert all(8*eps < v < 12*eps for v in q[h])
        assert sum(p[h])+sum(q[h]) < 61*eps < 1
    for i in range(r):
        for j in range(5):
            score = sum((a[h][i]+b[h][j])/(1-p[h][i]-q[h][j]) for h in range(2))
            assert rows[i][j]*score > 0
    # Full-cube positivity has already been checked by the exact all-one
    # minimum. For the smallest tables also exhaust every Boolean input.
    if r <= 2:
        for z in product((0,1), repeat=r):
            for w in product((0,1), repeat=5):
                for h in range(2):
                    assert 1-sum(pi*zi for pi,zi in zip(p[h],z))-sum(qj*wj for qj,wj in zip(q[h],w)) > 0
    return r*5


def main():
    total = 0
    for eps in (F(1,100), F(1,1000), F(1,1000000)):
        for r in (1,2,7,32,101):
            total += check_table(r,eps)
    print(f"Exact compact construction passed: {total} grid signs; all 32 patterns at each of three scales.")
    print("All slopes strictly negative and all full-cube denominator minima strictly positive.")


if __name__ == '__main__':
    main()
