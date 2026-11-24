#!/usr/bin/env python3
"""Exact finite checks for cauchy-krylov-leading-audit.tex."""
from fractions import Fraction as F
from random import Random


def rank(vectors):
    if not vectors:
        return 0
    a = [list(map(F, v)) for v in vectors]
    row = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        scale = a[row][col]
        a[row] = [z / scale for z in a[row]]
        for i in range(row + 1, len(a)):
            scale = a[i][col]
            if scale:
                a[i] = [u - scale * v for u, v in zip(a[i], a[row])]
        row += 1
        if row == len(a):
            break
    return row


def vectors(nodes, weights, order):
    return [
        [x ** j * y for x, y in zip(nodes, weights[k])]
        for k in range(order + 1)
        for j in range(order - k + 1)
    ]


def audit(nodes, weights, rng):
    increments = []
    previous_dimension = 0
    checks = 0
    for order in range(len(weights)):
        current = vectors(nodes, weights, order)
        dim = rank(current)
        increment = dim - previous_dimension
        increments.append(increment)
        assert increment <= (increments[-2] if order else 0) + 1
        assert increment * (increment + 1) <= 2 * len(nodes)
        previous = vectors(nodes, weights, order - 1) if order else []
        recurrence = previous + [[x * y for x, y in zip(nodes, v)]
                                 for v in previous] + [weights[order]]
        assert rank(recurrence) == dim
        assert rank(current + recurrence) == dim
        sign_input = [rng.choice((-1, 1)) for _ in nodes]
        time = F(7, 3)
        coefficient = sum(
            F(sign_input[h]) * weights[k][h] * nodes[h] ** (order - k)
            / time ** (order - k + 1)
            for h in range(len(nodes)) for k in range(order + 1)
        )
        polynomial = sum(
            time ** k * sum(F(s) * x ** (order - k) * y
                            for s, x, y in zip(sign_input, nodes, weights[k]))
            for k in range(order + 1)
        )
        assert coefficient == polynomial / time ** (order + 1)
        previous_dimension = dim
        checks += 1
    assert sum(increments) <= len(nodes)
    return increments, checks


def main():
    rng = Random(20261124)
    checks = 0
    for heads in range(1, 10):
        for _ in range(4):
            nodes = [F(rng.randrange(-4, 7), 3) for _ in range(heads)]
            weights = [[F(rng.randrange(-3, 4), 5) for _ in nodes]
                       for _ in range(7)]
            _, count = audit(nodes, weights, rng)
            checks += count
    for depth in range(1, 5):
        heads = depth * (depth + 1) // 2
        nodes = [F(i + 1) for i in range(heads)]
        weights = [[x ** (k * depth) for x in nodes] for k in range(depth)]
        increments, count = audit(nodes, weights, rng)
        assert increments == list(range(1, depth + 1))
        checks += count
    print(f"PASS: {checks} exact filtration/coefficient cases; sharp increments 1..4")


if __name__ == "__main__":
    main()
