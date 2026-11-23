#!/usr/bin/env python3
"""Exact rank and paired-order support checks; no asymptotic proof."""
from itertools import product
from random import Random
import sympy as S


def rank_check(heads):
    size = 2 ** (heads + 1) - 2
    rng = Random(701 + heads)
    u = [[rng.randint(1, 9) for _ in range(size)] for _ in range(heads)]
    v = [[rng.randint(1, 9) for _ in range(size)] for _ in range(heads)]
    a = [[rng.randint(-9, 9) for _ in range(size)] for _ in range(heads)]
    b = [[rng.randint(-9, 9) for _ in range(size)] for _ in range(heads)]
    base = [1 + sum(u[h]) + sum(v[h]) for h in range(heads)]
    # B_h(z,w) = base_h - sum u_hi z_i - sum v_hj w_j.
    assert all(base[h] - sum(u[h]) - sum(v[h]) == 1 for h in range(heads))
    assert all(x > 0 for row in u + v for x in row)
    p = [[base[h] - u[h][i] for i in range(size)] for h in range(heads)]
    q = [[-v[h][j] for j in range(size)] for h in range(heads)]
    def direct(i, j):
        return sum((a[h][i] + b[h][j]) * S.prod(p[g][i] + q[g][j]
                    for g in range(heads) if g != h) for h in range(heads))
    def grouped(i, j):
        ans = 0
        for bits in product((False, True), repeat=heads):
            left = [h for h in range(heads) if bits[h]]
            right = [h for h in range(heads) if not bits[h]]
            rs = S.prod(p[g][i] for g in left)
            us = sum(a[h][i] * S.prod(p[g][i] for g in left if g != h) for h in left)
            tc = S.prod(q[g][j] for g in right)
            vc = sum(b[h][j] * S.prod(q[g][j] for g in right if g != h) for h in right)
            ans += us * tc + rs * vc
        return ans
    matrix = S.Matrix(size, size, direct)
    assert all(matrix[i, j] == grouped(i, j) for i in range(size) for j in range(size))
    rank = matrix.rank()
    assert rank == size
    return {"heads": heads, "size": size, "exact_rank": rank,
            "full_cube_denominator_minimum": 1}


def orders_check(block_sizes):
    blocks = []
    for k, (left, right) in enumerate(block_sizes):
        blocks.append(([('a', k, i) for i in range(left)],
                       [('b', k, j) for j in range(right)]))
    first = [x for left, right in blocks for x in left + right]
    second = [x for left, right in reversed(blocks)
              for x in list(reversed(left)) + list(reversed(right))]
    ranks = [{x: i for i, x in enumerate(order)} for order in (first, second)]
    for x in first:
        for y in first:
            if x == y:
                continue
            vote = sum(1 if rank[x] < rank[y] else -1 for rank in ranks)
            expected = 0
            if x[1] == y[1] and x[0] != y[0]:
                expected = 2 if x[0] == 'a' else -2
            assert vote == expected
    return {"components": len(blocks), "vertices": len(first), "exact_support": True}


if __name__ == '__main__':
    for h in (1, 2, 3):
        print(rank_check(h))
    for blocks in ([(1, 1)], [(2, 1), (1, 3)], [(1, 2)] * 6):
        print(orders_check(blocks))
    print('All exact checks passed; neither global target is established.')
