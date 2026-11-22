#!/usr/bin/env python3
"""Exact finite checks for the proved open-code reciprocal-jet construction.

The general theorem is the written argument, not an extrapolation from these
examples. Modular nonzero determinants certify corresponding rational minors.
"""
from fractions import Fraction
from pathlib import Path
import json
import numpy as np


def syndrome(word: int, m: int) -> int:
    result = 0
    for g in range(m):
        if word >> g & 1:
            result ^= g
    return result


def determinant_mod(matrix: np.ndarray, prime: int) -> int:
    a = matrix.copy()
    det = 1
    for j in range(len(a)):
        pivots = np.flatnonzero(a[j:, j])
        if not len(pivots):
            return 0
        k = j + int(pivots[0])
        if k != j:
            a[[j, k]] = a[[k, j]]
            det = -det
        pivot = int(a[j, j])
        det = det * pivot % prime
        row = a[j, j:] * pow(pivot, -1, prime) % prime
        for k in range(j + 1, len(a)):
            a[k, j:] = (a[k, j:] - int(a[k, j]) * row) % prime
    return det % prime


def check(n: int, prime: int = 65521) -> dict:
    N = 1 << n
    m = 1 << ((n // 2).bit_length() - 1)
    mask = (1 << m) - 1
    codes = [c for c in range(1 << m) if syndrome(c, m) == 0]
    assert len(codes) * m == 1 << m
    centers = []
    pairs = []
    for y in range(N):
        s1 = syndrome(y & mask, m)
        s2 = syndrome((y >> m) & mask, m)
        pair = (1 << s1) | (1 << (m + s2))
        center = y ^ pair
        assert syndrome(center & mask, m) == 0
        assert syndrome((center >> m) & mask, m) == 0
        centers.append(center)
        pairs.append(pair)
    V = sorted(set(centers))
    q = len(V)
    assert q * m * m == N
    assert all(centers.count(v) == m * m for v in V)
    epsilon = Fraction(1, 4 * N)
    degree_bound = 3 * N * (q - 1)
    # Try grid points in their specified order. The theorem guarantees a
    # rational nonsingular point. A modular certificate can fail at a bad prime,
    # so this finite verifier checks only a small prefix with a stated prime.
    checks = 0
    for x in range(N):
        for y in range(N):
            diff = x ^ centers[y]
            E = int(diff & pairs[y] == pairs[y])
            a = 2 - diff.bit_count()
            assert E in (0, 1)
            assert epsilon + a != 0
            if x == y:
                assert a == 0 and E == 1
            elif a == 0:
                assert E == 0
            checks += 1
    assert N * 8 * epsilon**3 < 1
    for j in range(1, min(degree_bound + 2, 11)):
        delta = Fraction(j, (degree_bound + 2) * (n + 3))
        assert 0 < delta < Fraction(1, n + 3)
        matrix = np.zeros((N, N), dtype=np.int64)
        for v in V:
            assert 1 + delta * (epsilon + 1 - v.bit_count()) > 0
            assert 1 - 2 * delta > 0
        skipped = False
        for x in range(N):
            for y in range(N):
                diff = x ^ centers[y]
                E = int(diff & pairs[y] == pairs[y])
                B = (1 - delta) * (1 + x.bit_count()) + delta * (
                    epsilon + 2 - diff.bit_count())
                assert B > 0
                if B.numerator % prime == 0 or B.denominator % prime == 0:
                    skipped = True
                    break
                if E:
                    matrix[x, y] = pow(
                        B.denominator * pow(B.numerator, -1, prime) % prime,
                        3, prime)
            if skipped:
                break
        if skipped:
            continue
        det = determinant_mod(matrix, prime)
        if det:
            return dict(n=n, vertices=N, block_size=m, centers=q,
                        isolation_checks=checks, epsilon=str(epsilon),
                        determinant_degree_bound=degree_bound,
                        chosen_grid_index=j, delta=str(delta), prime=prime,
                        determinant_mod_prime=det,
                        rational_matrix_nonsingular=True)
    raise AssertionError("No modular certificate in tested grid prefix")


if __name__ == "__main__":
    results = [check(n) for n in (2, 3, 4, 5, 6, 7, 8)]
    destination = Path(__file__).with_name("open-code-pole-checks.json")
    destination.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
