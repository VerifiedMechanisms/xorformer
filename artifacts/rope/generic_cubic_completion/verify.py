#!/usr/bin/env python3
"""Exact arithmetic checks for a generic fourteen-coordinate pure cubic.

This verifies scalar pure admissibility, mixed denominator directions, and all
cross-Hessian minors used in the completion argument. It does not certify a
Boolean head-count separation.
"""

from fractions import Fraction as F
from itertools import combinations


def det(a):
    a = [row[:] for row in a]
    result = F(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        p = a[j][j]
        result *= p
        for i in range(j + 1, len(a)):
            q = a[i][j] / p
            for k in range(j + 1, len(a)):
                a[i][k] -= q * a[j][k]
    return result


def matmul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def transpose(a):
    return [list(row) for row in zip(*a)]


def main():
    size = 14
    s = [[F(i ** h, 10000) for i in range(1, size + 1)] for h in range(3)]
    b = [[(F(i) ** (h + 3) - F(15, 2) ** (h + 3)) / 10**9
          for i in range(1, size + 1)] for h in range(3)]
    for h in range(3):
        assert all(s[h][i] > abs(b[h][i]) for i in range(size))
        assert sum(s[h]) < 1
        assert min(b[h]) < 0 < max(b[h])
        assert all(b[h])
    rows = [[s[h][i] for h in range(3)] + [b[h][i] for h in range(3)]
            for i in range(size)]
    # Six-column basis differs from (1,t,...,t^5) by invertible scaling and
    # subtraction of constant multiples of its first column.
    for indices in combinations(range(size), 6):
        vandermonde = F(1, 10000**3 * 10**27)
        for i, j in combinations(indices, 2):
            vandermonde *= j - i
        assert det([rows[i] for i in indices]) == vandermonde != 0
    checked = 0
    for k in range(size):
        u, beta = rows[k][:3], rows[k][3:]
        hess = [[F(0) for _ in range(6)] for _ in range(6)]
        for i in range(3):
            for j in range(3):
                if i != j:
                    other = 3 - i - j
                    hess[i][j + 3] = hess[j + 3][i] = beta[other]
                    hess[i + 3][j + 3] = u[other]
        assert det(hess) == -4 * (beta[0] * beta[1] * beta[2])**2 != 0
        full = matmul(matmul(rows, hess), transpose(rows))
        for i in range(size):
            if i == k:
                continue
            rest = [j for j in range(size) if j not in (i, k)]
            a, bb = rest[:6], rest[6:]
            cross = [[full[x][y] for y in bb] for x in a]
            expected = det([rows[x] for x in a]) * det(hess) * det([rows[y] for y in bb])
            assert det(cross) == expected != 0
            checked += 1
    print(f"exact checks passed: 42 pure mass bounds, 3003 Vandermonde minors, {checked} Hessian cross minors")
    print("scope: cubic coefficient completion; no Boolean head-count separation claimed")


if __name__ == "__main__":
    main()
