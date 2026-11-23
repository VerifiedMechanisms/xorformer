#!/usr/bin/env python3
"""Exact finite certificates for the reciprocal/Segre Jacobian comparison.

All arithmetic is modulo a prime. Full rank modulo this prime certifies
full rank over Q at the explicitly specified positive rational points.
This is a small-instance formula check, not a replacement for CGG's theorem.
"""

from random import Random


PRIME = 1_000_003


def rank_mod(matrix):
    a = [row[:] for row in matrix]
    rank = 0
    for col in range(len(a[0])):
        pivot = next((j for j in range(rank, len(a)) if a[j][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][col], -1, PRIME)
        a[rank] = [x * inv % PRIME for x in a[rank]]
        for j in range(rank + 1, len(a)):
            factor = a[j][col]
            if factor:
                a[j] = [(x - factor * y) % PRIME
                        for x, y in zip(a[j], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def main():
    rng = Random(20261123)
    epsilon = pow(1000, -1, PRIME)
    for n in range(1, 7):
        dimension = 1 << n
        heads = (dimension + n) // (n + 1)
        # All c_h = 1, all v_hi are positive integers in [1, 50].
        vectors = [[rng.randrange(1, 51) for _ in range(n)]
                   for _ in range(heads)]
        segre, reciprocal = [], []
        for bits in range(dimension):
            sr, rr = [], []
            for v in vectors:
                selected = [i for i in range(n) if bits >> i & 1]
                product = 1
                for i in selected:
                    product = product * v[i] % PRIME
                sr.append(product)
                sr.extend(product * pow(v[i], -1, PRIME) % PRIME
                          if i in selected else 0 for i in range(n))
                denominator = (1 + epsilon * sum(v[i] for i in selected)) % PRIME
                assert denominator
                inverse = pow(denominator, -1, PRIME)
                rr.append(inverse)
                rr.extend(-epsilon * inverse * inverse % PRIME
                          if i in selected else 0 for i in range(n))
            segre.append(sr)
            reciprocal.append(rr)
        ranks = rank_mod(segre), rank_mod(reciprocal)
        assert ranks == (dimension, dimension), (n, ranks)
        print(f"n={n}, R={heads}, parameters={heads*(n+1)}, "
              f"Segre rank={ranks[0]}, reciprocal rank={ranks[1]}")


if __name__ == "__main__":
    main()
