#!/usr/bin/env python3
"""Exact finite checks for the four-head local orientation obstructions."""

from itertools import product


def insert(table, z, label):
    z = tuple(z)
    assert z not in table or table[z] == label
    table[z] = label


def orbit(table):
    answer = {}
    for z, label in table.items():
        for flip in (-1, 1):
            for t in (-1, 1):
                insert(answer, tuple(flip * a for a in z) + (t,), t * label)
    return answer


def initial():
    table = {}
    base = (-1,) * 16
    insert(table, base, -1)
    for i in range(16):
        z = list(base)
        z[i] = 1
        insert(table, z, 1)
    for i, j in product(range(8), repeat=2):
        if i != j:
            z = list(base)
            z[2 * i] = z[2 * j + 1] = 1
            insert(table, z, -1)
    return table


def q_integer(z, delta=0):
    x, y = z[::2], z[1::2]
    sx, sy = sum(x), sum(y)
    return (192 - 3 * (sx * sx + sy * sy)
            + 180 * sum(a * b for a, b in zip(x, y))
            + 2 * x[0] * y[0] - 20 * sx * sy
            + delta * (y[4] - y[5]) * (y[6] - y[7]))


old = initial()
for i in range(8):
    for j in range(i + 1, 8):
        z = [-1] * 16
        z[2 * i + 1] = z[2 * j + 1] = 1
        insert(old, z, -1)
assert len(old) == 101
assert len(orbit(old)) == 404

new = initial()
middle = {}
for j in range(8):
    plus = {1, 2, 3} if j == 0 else {0, *[k for k in range(1, 8) if k != j][:2]}
    for s, a in product((-1, 1), repeat=2):
        y = [a if k == j else s * (1 if k in plus else -1) for k in range(8)]
        z = [v for b in y for v in (-1, b)]
        insert(middle, z, -a)
        insert(new, z, -a)
assert len(middle) == 18
assert len(new) == 91
assert len(orbit(new)) == 364
for z, label in new.items():
    assert label * q_integer(z) > 0
    y = z[1::2]
    assert (y[4] - y[5]) * (y[6] - y[7]) == 0

minimum = {0: None, 20: None}
for z in product((-1, 1), repeat=16):
    for delta in minimum:
        q = q_integer(z, delta)
        assert q % 4 == 2
        minimum[delta] = abs(q) if minimum[delta] is None else min(minimum[delta], abs(q))
for z, label in orbit(new).items():
    for delta in minimum:
        assert label * z[-1] * q_integer(z[:-1], delta) > 0

print("404-point original pattern and 364-point cross-only pattern counted exactly.")
print("All prescribed labels and the free quadratic perturbation verified with integers.")
print("Both explicit quadratic completions are nonzero on all 65,536 inputs.")
print("Minimum absolute integer scores:", minimum)
