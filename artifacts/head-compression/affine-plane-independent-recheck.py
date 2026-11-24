#!/usr/bin/env python3
"""Independent exact replay of the affine-plane compiler from 7065e81.

This checks finite examples, not the universal theorem. It constructs every
affine numerator and denominator, including the rank-factor offset head and
the exact weight-two strictification. Whole-cube positivity is checked by the
exact minimum of each affine denominator. Axis repair is a separate theorem.
"""

from fractions import Fraction as Q
from itertools import product
from random import Random


def solve(a, y):
    a = [list(row) + [v] for row, v in zip(a, y)]
    for j in range(len(a)):
        pivot = next(i for i in range(j, len(a)) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        d = a[j][j]
        a[j] = [v / d for v in a[j]]
        for i in range(len(a)):
            if i != j:
                d = a[i][j]
                a[i] = [u - d * v for u, v in zip(a[i], a[j])]
    return [row[-1] for row in a]


def field(k):
    # Primitive irreducibles over F_2, for the small checked examples only.
    modulus = {1: 0b11, 2: 0b111, 3: 0b1011}[k]
    q = 1 << k

    def mul(a, b):
        z = 0
        while b:
            if b & 1:
                z ^= a
            b >>= 1
            a <<= 1
            if a & q:
                a ^= modulus
        return z

    def div(a, b):
        assert b
        return next(c for c in range(q) if mul(b, c) == a)

    for a, b, c in product(range(q), repeat=3):
        assert mul(a, b ^ c) == mul(a, b) ^ mul(a, c)
        assert mul(a, mul(b, c)) == mul(mul(a, b), c)
    for a in range(1, q):
        assert mul(a, div(1, a)) == 1
    return mul, div


def strictify(head):
    numerator, b0, slopes = head
    assert all(v <= 0 for v in slopes)
    minimum = b0 + sum(slopes)
    assert minimum > 0
    eps = minimum / (len(slopes) + 1)
    return numerator, b0 + 2 * eps, [v - eps for v in slopes]


def run(k, table):
    q = 1 << k
    r, s = len(table), len(table[0])
    assert 1 <= r <= k * q * q and s > 0
    mul, div = field(k)
    points = list(product(range(q), repeat=2))
    rows = [(p, bit) for p in points for bit in range(k)][:r]
    delta = Q(1, 4 * (r + s + 1))
    token = [delta * Q(z + 1, q + 1) for z in range(q)]
    pole = [1 - v for v in token]
    cauchy = [[1 / (pole[a] - token[z]) for a in range(q)] for z in range(q)]
    eta = [solve(cauchy, [Q(1 if (z >> bit) & 1 else -1)
                         for z in range(q)]) for bit in range(k)]
    labels = {row: values for row, values in zip(rows, table)}
    memory = {p: [sum((labels.get((p, bit), [-1] * s)[j] > 0) << bit
                      for bit in range(k)) for j in range(s)] for p in points}
    zline = {(a, c): [sum(1 / (pole[a] - token[memory[g][j]])
                              for g in points if g[1] == mul(a, g[0]) ^ c)
                      for j in range(s)] for a, c in points}
    heads = []
    correction = [Q(0)] * s
    for a, c in points:
        f = [eta[bit][a] if c == h[1] ^ mul(a, h[0]) else Q(0)
             for h, bit in rows]
        g = zline[a, c]
        shift = 1 + sum(abs(v) for v in f)
        u = [shift + v for v in f]
        scale = 4 * (r + 1) * shift
        head = ([Q(0)] * r + [scale * v for v in g], Q(1),
                [-v / (scale + v) for v in u] + [Q(0)] * s)
        heads.append(strictify(head))
        correction = [v - (scale + shift) * w for v, w in zip(correction, g)]
    heads.append(strictify(([Q(0)] * r + correction, Q(1), [Q(0)] * (r + s))))
    for g in points:
        slopes, numerator = [], []
        for h, bit in rows:
            different = h[0] != g[0]
            a = div(g[1] ^ h[1], g[0] ^ h[0]) if different else 0
            slopes.append(pole[a] - 1)
            numerator.append(-eta[bit][a] if different else Q(0))
        heads.append((numerator + [Q(0)] * s, Q(1),
                      slopes + [-token[memory[g][j]] for j in range(s)]))
    assert len(heads) == 2 * q * q + 1
    for numerator, b0, slopes in heads:
        assert len(numerator) == len(slopes) == r + s
        assert all(v < 0 for v in slopes)
        assert b0 + sum(slopes) > 0  # Exact whole-cube minimum.
        if r + s <= 6:
            for bits in product((0, 1), repeat=r + s):
                assert b0 + sum(v * x for v, x in zip(slopes, bits)) > 0
    for i, j in product(range(r), range(s)):
        score = sum((a[i] + a[r + j]) / (b0 + b[i] + b[r + j])
                    for a, b0, b in heads)
        assert score == table[i][j], (k, r, s, i, j, score)
    return r * s, len(heads)


def main():
    tables, scores, heads = 0, 0, 0
    for word in product((-1, 1), repeat=8):
        c, h = run(1, [word[2 * i:2 * i + 2] for i in range(4)])
        tables, scores, heads = tables + 1, scores + c, heads + h
    rng = Random(20261124)
    for k, r, s, count in [(2, 7, 3, 5), (2, 17, 1, 5),
                            (2, 32, 3, 5), (3, 192, 2, 2)]:
        for _ in range(count):
            table = [[rng.choice((-1, 1)) for _ in range(s)] for _ in range(r)]
            c, h = run(k, table)
            tables, scores, heads = tables + 1, scores + c, heads + h
    print(f"PASS: {tables} tables, {scores} exact target scores, {heads} strict heads")
    print("All 256 binary 4x2 tables; sampled F4/F8 full and truncated row encodings.")
    print("Each head's exact whole-cube minimum is positive; no axis repair tested here.")


if __name__ == '__main__':
    main()
