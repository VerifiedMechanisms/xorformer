#!/usr/bin/env python3
"""Exact small-cube check of row/column multipliers and shared correction."""
from fractions import Fraction as F
from itertools import product


def value(head, bits):
    a0, aa, b0, bb = head
    return (a0 + sum(a*x for a, x in zip(aa, bits))) / (
        b0 + sum(b*x for b, x in zip(bb, bits)))


def strictify(head):
    a0, aa, b0, bb = head
    delta = b0 + sum(bb)
    assert delta > 0 and all(b <= 0 for b in bb)
    eps = delta / (len(bb) + 1)
    return a0, aa, b0 + 2*eps, [b-eps for b in bb]


def multiply_rows(heads, bias, r, s, coeff):
    out = []
    baseline = [F(0) for _ in range(s)]
    for a0, aa, b0, bb in heads:
        for j in range(s):
            baseline[j] += aa[r+j] / (b0 + bb[r+j])
        out.append((F(0), [a0+aa[i] if coeff[i] == 1 else F(0) for i in range(r)]
                    + aa[r:], b0,
                    [bb[i] if coeff[i] == 1 else F(0) for i in range(r)] + bb[r:]))
        out.append((F(0), [-a0-aa[i] if coeff[i] == -1 else F(0) for i in range(r)]
                    + [-a for a in aa[r:]], b0,
                    [bb[i] if coeff[i] == -1 else F(0) for i in range(r)] + bb[r:]))
    C = F(1) + sum(abs(x) for x in coeff)
    M = 4*(r+1)*C
    uu = [C+x for x in coeff]
    out.append((F(0), [F(0)]*r + [M*q for q in baseline], F(1),
                [-u/(M+u) for u in uu] + [F(0)]*s))
    out.append((F(0), [x*bias for x in coeff]
                + [-(M+C)*q for q in baseline], F(1), [F(0)]*(r+s)))
    return [strictify(h) for h in out]


def main():
    r, s, H = 3, 2, 3
    heads = []
    for h in range(H):
        aa = [F((h+2)*(k+1)-7, k+1) for k in range(r+s)]
        bb = [-F((h+1)*(k+1), 7) for k in range(r+s)]
        heads.append((F(h-2), aa, F(20)+sum(-b for b in bb), bb))
    bias = F(3, 7)
    for coeff in product(map(F, [-1, 0, 1]), repeat=r):
        out = multiply_rows(heads, bias, r, s, coeff)
        assert len(out) == 2*H+2
        for h in out:
            assert all(b < 0 for b in h[3])
            for bits in product([0, 1], repeat=r+s):
                assert h[2] + sum(b*x for b, x in zip(h[3], bits)) > 0
        for i in range(r):
            for j in range(s):
                bits = [int(k == i) for k in range(r)] + [int(k == j) for k in range(s)]
                assert sum(value(h, bits) for h in out) == coeff[i]*(
                    bias+sum(value(h, bits) for h in heads))
    print('PASS: all27 ternary row masks,6 grid points,8 heads,32 full-cube vertices; exact rational arithmetic')


if __name__ == '__main__':
    main()
