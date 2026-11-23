#!/usr/bin/env python3
"""Exact finite checks for balanced codebook assignments, not a compiler."""
from fractions import Fraction as Q
from itertools import product
from math import ceil, log
from random import Random


def inverse(a):
    n = len(a)
    b = [list(row) + [Q(i == j) for j in range(n)] for i, row in enumerate(a)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if b[i][j])
        b[j], b[pivot] = b[pivot], b[j]
        factor = b[j][j]
        b[j] = [x / factor for x in b[j]]
        for i in range(n):
            if i != j:
                factor = b[i][j]
                b[i] = [x - factor * y for x, y in zip(b[i], b[j])]
    return [row[n:] for row in b]


def check_balance(seed, blocks, colors, columns):
    rng = Random(seed)
    a = [[rng.randrange(colors) for _ in range(columns)] for _ in range(blocks)]
    limit = ceil(2 * blocks / colors + log(columns * colors) + 1)
    for attempt in range(10000):
        shift = [rng.randrange(colors) for _ in range(blocks)]
        assignments = [[(a[b][j] + shift[b]) % colors for b in range(blocks)]
                       for j in range(columns)]
        if all(max(labels.count(c) for c in range(colors)) <= limit
               for labels in assignments):
            break
    else:
        raise AssertionError("finite search did not find a witness")
    groups = colors * limit
    for j, labels in enumerate(assignments):
        for c in range(colors):
            labels.extend([c] * (limit - labels.count(c)))
        assert len(labels) == groups
        assert all(labels.count(c) == limit for c in range(colors))
        assert all((labels[b] - shift[b]) % colors == a[b][j] for b in range(blocks))
        residues = [Q(rng.randrange(-4, 5)) for _ in range(blocks)] + [Q(0)] * (groups - blocks)
        profile = [Q(rng.randrange(-4, 5)) for _ in range(colors)]
        query = Q(1)
        poles = [Q(g + 1, 1000 * (groups + 1)) for g in range(groups)]
        whole = sum(residues[g] * profile[labels[g]] / (query - poles[g]) ** 2
                    for g in range(groups))
        active = sum(residues[g] * profile[labels[g]] / (query - poles[g]) ** 2
                     for g in range(blocks))
        assert whole == active
    return {"seed": seed, "blocks": blocks, "colors": colors,
            "columns": columns, "groups": groups, "attempt": attempt}


def check_codebook(k=2, bits=3):
    c = [[1 / (Q(1) - Q(i + 1, 100) - Q(j + 1, 1000)) ** 2
          for j in range(k)] for i in range(k)]
    ci = inverse(c)
    vectors = set()
    for word in product((-1, 1), repeat=k * bits):
        s = [list(word[i * bits:(i + 1) * bits]) for i in range(k)]
        w = [[sum(ci[i][h] * s[h][j] for h in range(k))
              for j in range(bits)] for i in range(k)]
        assert all(sum(c[i][h] * w[h][j] for h in range(k)) == s[i][j]
                   for i in range(k) for j in range(bits))
        vectors.update(map(tuple, w))
    assert len(vectors) <= k * 2 ** (k * bits)
    return {"block_size": k, "bits": bits, "codebook_size": len(vectors),
            "upper_bound": k * 2 ** (k * bits)}


if __name__ == "__main__":
    for seed in range(5):
        print(check_balance(seed, 128, 8, 32))
    print(check_codebook())
    print("Exact finite identities passed. Cross-block isolation remains unproved.")
