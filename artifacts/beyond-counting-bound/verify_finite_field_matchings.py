"""Exact finite checks for the explicit multiaffine-shattering construction.

The asymptotic theorem has a written proof. This program independently checks
the finite-field incidence data and matching examples for q=4 and q=8. It is
not an attention-head lower-bound computation.
"""

import itertools
import json
from pathlib import Path
import random


def check(q, modulus):
    def mul(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & q:
                a ^= modulus
        return result

    table = [[mul(a, b) for b in range(q)] for a in range(q)]
    assert all(table[a][1] == a for a in range(q))
    assert all(1 in table[a] for a in range(1, q))
    for a, b, c in itertools.product(range(q), repeat=3):
        assert table[a][b] == table[b][a]
        assert table[table[a][b]][c] == table[a][table[b][c]]
        assert table[a][b ^ c] == table[a][b] ^ table[a][c]

    points = list(itertools.product(range(q), repeat=3))
    directions = [a for a in points if a != (0, 0, 0)
                  and next(t for t in a if t) == 1]
    assert len(directions) == q*q + q + 1
    partitions = []
    planes = []
    for a in directions:
        fibers = [[] for _ in range(q)]
        for index, point in enumerate(points):
            color = table[a[0]][point[0]] ^ table[a[1]][point[1]] ^ table[a[2]][point[2]]
            fibers[color].append(index)
        assert all(len(fiber) == q*q for fiber in fibers)
        partitions.append(fibers)
        planes.extend(sum(1 << point for point in fiber) for fiber in fibers)
    assert len(set(planes)) == len(planes)
    maximum_intersection = 0
    for i, a in enumerate(planes):
        for b in planes[:i]:
            size = (a & b).bit_count()
            assert size <= q
            maximum_intersection = max(maximum_intersection, size)

    repetitions = q//2 - 1
    maps = [part for part in partitions for _ in range(repetitions)]
    p, m = len(points), len(maps)
    assert 2*m < p
    assert 2*((q+1)*q*q - (q+1)*q//2*q) > p
    assert repetitions*q < q*q

    rng = random.Random(281828 + q)
    assignments = [[0]*m, [q-1]*m]
    assignments += [[rng.randrange(q) for _ in range(m)] for _ in range(20)]
    for target in assignments:
        owner = [-1]*p

        def augment(i, seen):
            for point in maps[i][target[i]]:
                if point in seen:
                    continue
                seen.add(point)
                if owner[point] < 0 or augment(owner[point], seen):
                    owner[point] = i
                    return True
            return False

        for i in range(m):
            assert augment(i, set())
        selected = [None]*m
        for point, i in enumerate(owner):
            if i >= 0:
                selected[i] = point
        assert len(set(selected)) == m
        assert all(selected[i] in maps[i][target[i]] for i in range(m))
        permutation = selected + [point for point in range(p) if owner[point] < 0]
        assert sorted(permutation) == list(range(p))

    return dict(q=q, parameters=p, directions=len(directions),
                distinct_planes=len(planes), plane_size=q*q,
                maximum_pair_intersection=maximum_intersection,
                repeated_maps=m, shattered_tests=m*(q.bit_length()-1),
                checked_matchings=len(assignments), exact_checks_passed=True)


if __name__ == '__main__':
    results = [check(4, 0b111), check(8, 0b1011)]
    output = Path(__file__).with_name('finite-field-matching-verification.json')
    output.write_text(json.dumps(results, indent=2)+'\n')
    print(json.dumps(results))
