#!/usr/bin/env python3
"""Exact rational finite checks for adaptive-barycentric-root.tex."""
from fractions import Fraction as F
from itertools import product


def mul(a, b):
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c


def evaluate(a, x):
    out = F(0)
    for v in reversed(a):
        out = out * x + v
    return out


def polynomial(roots):
    out = [F(1)]
    for x in roots:
        out = mul(out, [-x, F(1)])
    return out


words = moments = 0
max_scale_bits = 0
for m in range(1, 7):
    centers = [F(s + 1, 10 * m) for s in range(m)]
    queries = [1 - x for x in centers]
    pd = [F(1)] * m
    for i, x in enumerate(centers):
        for j, y in enumerate(centers):
            if i != j:
                pd[i] *= x - y
    for sigma in product((-1, 1), repeat=m):
        points = centers + queries[::-1]
        signs = [sigma[i] * (-1) ** (m - i - 1) for i in range(m)] + list(sigma[::-1])
        roots = [(points[i] + points[i + 1]) / 2 for i in range(2 * m - 1)
                 if signs[i] != signs[i + 1]]
        assert len(roots) == m - 1
        r = [sigma[0] * a for a in polynomial(roots)]
        assert all(signs[i] * evaluate(r, points[i]) > 0 for i in range(2 * m))
        d = [1 / abs(pd[i] * evaluate(r, x)) for i, x in enumerate(centers)]
        scale = 1
        while True:
            poles = [v for i, x in enumerate(centers) for v in (x - d[i] / scale, x + d[i] / scale)]
            if not all(poles[i] < poles[i + 1] for i in range(2 * m - 1)) or poles[-1] >= min(queries):
                scale *= 2
                continue
            residues = []
            for i, x in enumerate(poles):
                derivative = F(1)
                for j, y in enumerate(poles):
                    if i != j:
                        derivative *= x - y
                residues.append(1 / derivative)
            scores = [sum(sigma[j] * (residues[2*j+1] / (t-poles[2*j+1])
                                      - residues[2*j] / (t-poles[2*j])) for j in range(m))
                      for t in queries]
            child_limits = [evaluate(r, x) / (2 * pd[i]) for i, x in enumerate(centers)]
            left = [residues[2*i + (1 if sigma[i] == 1 else 0)] / scale for i in range(m)]
            right = [residues[2*i + (0 if sigma[i] == 1 else 1)] / scale for i in range(m)]
            if (all(s * y > 0 for s, y in zip(sigma, scores))
                    and all(abs(a-b) < max(F(1), abs(b))/100 for a, b in zip(left, child_limits))
                    and all(abs(a+b) < max(F(1), abs(b))/100 for a, b in zip(right, child_limits))):
                break
            scale *= 2
            assert scale.bit_length() < 2000
        for j in range(2 * m):
            moment = sum(c * x**j for c, x in zip(residues, poles))
            assert moment == (1 if j == 2 * m - 1 else 0)
            moments += 1
        for t in queries:
            q = F(1)
            for x in poles:
                q *= t - x
            assert sum(c / (t-x) for c, x in zip(residues, poles)) == 1/q
        words += 1
        max_scale_bits = max(max_scale_bits, scale.bit_length())

print(f"PASS: {words} sign words, {moments} exact moments, partial fractions and child limits; "
      f"largest scale has {max_scale_bits} bits")
