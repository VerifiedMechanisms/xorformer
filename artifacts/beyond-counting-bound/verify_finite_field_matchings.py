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

    points = list(itertools.product(range(q), repeat=2))
    directions = [a for a in points if a != (0, 0)
                  and next(t for t in a if t) == 1]
    assert len(directions) == q + 1
    partitions = []
    lines = []
    for a in directions:
        fibers = [[] for _ in range(q)]
        for index, point in enumerate(points):
            color = table[a[0]][point[0]] ^ table[a[1]][point[1]]
            fibers[color].append(index)
        assert all(len(fiber) == q for fiber in fibers)
        partitions.append(fibers)
        lines.extend(sum(1 << point for point in fiber) for fiber in fibers)
    assert len(set(lines)) == len(lines)
    maximum_intersection = 0
    for i, a in enumerate(lines):
        for b in lines[:i]:
            size = (a & b).bit_count()
            assert size <= 1
            maximum_intersection = max(maximum_intersection, size)

    repetitions = q//2
    maps = [part for part in partitions for _ in range(repetitions)]
    p, m = len(points), len(maps)
    assert m <= p
    assert (q+1)*q - (q+1)*q//2 == m
    assert all(k*q - k*(k-1)//2 >= k*repetitions for k in range(q+1))
    checked_small_sets = 0
    if q == 4:
        partition_masks = [[sum(1 << point for point in fiber) for fiber in part]
                           for part in partitions]
        for subset in range(1 << p):
            size = subset.bit_count()
            if size >= m:
                continue
            bad = repetitions*sum(any(line & subset == line for line in part)
                                  for part in partition_masks)
            assert bad <= size
            checked_small_sets += 1

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
                distinct_lines=len(lines), line_size=q,
                maximum_pair_intersection=maximum_intersection,
                repeated_maps=m, shattered_tests=m*(q.bit_length()-1),
                checked_matchings=len(assignments), checked_small_sets=checked_small_sets,
                exact_checks_passed=True)


if __name__ == '__main__':
    results = [check(4, 0b111), check(8, 0b1011)]
    output = Path(__file__).with_name('finite-field-matching-verification.json')
    output.write_text(json.dumps(results, indent=2)+'\n')
    print(json.dumps(results))
