"""Exact integer marginal checks and rank certificates modulo a prime.

This finite computation supports the written gluing induction. It is not Lean.
"""
from collections import Counter
import json

BASE = {(3, 1): -1, (2, 1): -1, (3, 2): 1, (0, 1): 1,
        (2, 3): -1, (0, 2): -2, (1, 0): -1, (0, 3): 1,
        (2, 0): 1, (2, 2): 1, (1, 1): 1}
INPUT, OUTPUT = (3, 2), (0, 2)
PRIME = 65537


def projections(p):
    return p[0], p[1], p[0] + p[1]


def rank_mod(matrix):
    matrix = [row[:] for row in matrix]
    rank = 0
    for col in range(len(matrix[0])):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][col] % PRIME), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inv = pow(matrix[rank][col], -1, PRIME)
        matrix[rank] = [(v * inv) % PRIME for v in matrix[rank]]
        for i in range(rank + 1, len(matrix)):
            factor = matrix[i][col]
            if factor:
                matrix[i] = [(a - factor * b) % PRIME
                             for a, b in zip(matrix[i], matrix[rank])]
        rank += 1
    return rank


def check(circuit, k):
    points = sorted(circuit)
    rows = []
    for direction in range(3):
        marginal = Counter()
        for point, coefficient in circuit.items():
            marginal[projections(point)[direction]] += coefficient
        assert all(value == 0 for value in marginal.values())
        for value in sorted(marginal):
            rows.append([int(projections(point)[direction] == value) for point in points])
    rank = rank_mod(rows)
    assert rank == len(points) - 1
    assert len(points) == 9 * k + 2
    assert max(map(abs, circuit.values())) == 2 ** k
    assert sum(map(abs, circuit.values())) == 10 * 2 ** k - 8
    assert any(abs(v) == 1 for v in circuit.values())
    return {'k': k, 'support': len(points), 'rank_mod_65537': rank,
            'max_coefficient': 2 ** k, 'coefficient_l1': 10 * 2 ** k - 8,
            'six_point_generator_occurrences': 3 * k,
            'generator_atom_occurrences': 18 * k}


def glue(circuit, output):
    radius = max(abs(v) for point in circuit for v in projections(point))
    scale = 10 * (radius + 10)
    def transform(p):
        return tuple(output[i] + scale * (p[i] - INPUT[i]) for i in range(2))
    new = {transform(p): c for p, c in BASE.items()}
    assert set(circuit) & set(new) == {output}
    for direction in range(3):
        old_values = {projections(p)[direction] for p in circuit}
        new_values = {projections(p)[direction] for p in new}
        assert old_values & new_values == {projections(output)[direction]}
    factor = -circuit[output]
    result = Counter(circuit)
    for p, c in new.items():
        result[p] += factor * c
    result = {p: c for p, c in result.items() if c}
    return result, transform(OUTPUT)


if __name__ == '__main__':
    circuit, output = dict(BASE), OUTPUT
    records = []
    for k in range(1, 13):
        records.append(check(circuit, k))
        circuit, output = glue(circuit, output)
    print(json.dumps({'prime': PRIME, 'base': [[*p, c] for p, c in BASE.items()],
                      'records': records}, indent=2))
