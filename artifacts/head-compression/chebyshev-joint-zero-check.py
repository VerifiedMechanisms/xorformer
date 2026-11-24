#!/usr/bin/env python3
"""Exact finite checks for chebyshev-joint-zero-family.tex.

Only rational quadratic/cubic fibers are used. The universal theorem is
proved in the accompanying note; finite testing does not establish it.
"""
from fractions import Fraction as F
from itertools import permutations, product


def chebyshev(k, x):
    if k == 0:
        return F(1)
    a, b = F(1), x
    for _ in range(1, k):
        a, b = b, 2 * x * b - a
    return b


def derivative(k, x):
    if k == 0:
        return F(0)
    a, b = F(1), 2 * x
    for _ in range(1, k - 1):
        a, b = b, 2 * x * b - a
    return k * (a if k == 1 else b)


def cubic_fiber(q):
    a = (q * q + q - F(1, 2)) / (q * q + q + 1)
    b = -F(1, 2) + q * (a - 1)
    return tuple(sorted((a, b, -a - b)))


def check(k, fibers):
    r, s = 4, len(fibers)
    eps, eta, eta0 = F(1, 1000), F(1, 100), F(1)
    # The cubic baseline derivative is large, so keep addresses very close.
    xs = [1 + F(i, 10**14) for i in range(r)]
    ts = [chebyshev(k, roots[0]) for roots in fibers]
    for roots, t in zip(fibers, ts):
        assert len(set(roots)) == k
        assert all(-1 < a < 1 for a in roots)
        assert -1 < t < 1
        assert all(chebyshev(k, a) == t for a in roots)

    C = chebyshev(k, 1 / eps)
    tmin = min(ts)
    base_constant = C - tmin + 2 * eta0
    base_rows = [eta0 + C - chebyshev(k, x / eps) for x in xs]
    base_cols = [t - tmin + eta0 for t in ts]
    assert min(base_rows + base_cols) > 0
    assert base_constant - sum(base_rows) - sum(base_cols) > 0

    head_constant = 1 + eps + 2 * eta
    head_rows = [eta + 1 - x for x in xs]
    perm_list = list(permutations(range(k)))
    count = 0
    for pis in product(perm_list, repeat=s):
        cols = [
            [eps + eps * fibers[j][pis[j][h]] + eta for j in range(s)]
            for h in range(k)
        ]
        for cs in cols:
            assert min(head_rows + cs) > 0
            assert head_constant - sum(head_rows) - sum(cs) > 0
        for i, x in enumerate(xs):
            for j, t in enumerate(ts):
                lhs = sum(
                    1 / (head_constant - head_rows[i] - cols[h][j])
                    for h in range(k)
                )
                baseline_den = base_constant - base_rows[i] - base_cols[j]
                assert baseline_den == chebyshev(k, x / eps) - t
                rhs = derivative(k, x / eps) / eps / baseline_den
                assert lhs == rhs
        count += 1

    # Explicitly enumerate every Boolean vertex for one tuple, in addition
    # to the all-one minimum checks for every tuple above.
    cube_count = 0
    for bits in product((0, 1), repeat=r + s):
        z, w = bits[:r], bits[r:]
        assert base_constant - sum(a*b for a, b in zip(base_rows, z)) \
            - sum(a*b for a, b in zip(base_cols, w)) > 0
        for cs in cols:
            assert head_constant - sum(a*b for a, b in zip(head_rows, z)) \
                - sum(a*b for a, b in zip(cs, w)) > 0
        cube_count += 1
    print(f"k={k}: {count} exact permutation tuples, "
          f"{r*s*count} zero grid scores, {cube_count} explicit cube vertices")


if __name__ == "__main__":
    check(2, [(-u, u) for u in (F(1, 4), F(1, 3), F(2, 5))])
    check(3, [cubic_fiber(F(q)) for q in (2, 3, 4)])
