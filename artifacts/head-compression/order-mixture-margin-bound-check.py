"""Exact finite order-mixture margin checks; no asymptotic claim from samples."""

from itertools import permutations
from math import comb, factorial


def comparison_tables(m):
    tables = set()
    for order in permutations(range(2 * m)):
        position = [0] * (2 * m)
        for k, item in enumerate(order):
            position[item] = k
        mask = sum(1 << (m * i + j)
                   for i in range(m) for j in range(m)
                   if position[i] < position[m + j])
        tables.add(mask)
    return tables


def check(m):
    n = m * m
    full = (1 << n) - 1
    tables = comparison_tables(m)
    assert len(tables) <= factorial(2 * m)
    assert 0 in tables and full in tables
    assert {v ^ full for v in tables} == tables
    correlations = {}
    for sigma in range(1 << n):
        correlations[sigma] = max(n - 2 * (sigma ^ v).bit_count()
                                  for v in tables)
    optimum = min(correlations.values())
    hard = min(s for s, c in correlations.items() if c == optimum)
    # Independent exact distribution of a fixed-order correlation.
    v = next(iter(tables))
    for changes in range(n + 1):
        value = n - 2 * changes
        count = sum(n - 2 * (s ^ v).bit_count() == value
                    for s in range(1 << n))
        assert count == comb(n, changes)
    print(f"m={m}, orders={factorial(2*m)}, distinct_tables={len(tables)}, "
          f"min_max_correlation={optimum}, relative_bound={optimum}/{n}")
    print("hard table:")
    for i in range(m):
        print(" ".join("+" if hard & (1 << (m*i+j)) else "-"
                       for j in range(m)))
    return len(tables), optimum


if __name__ == "__main__":
    assert check(2) == (14, 2)
    assert check(3) == (230, 5)
    print("All exact finite checks passed.")
