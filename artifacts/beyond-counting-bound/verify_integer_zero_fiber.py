"""Independent exact audit of the 16-bit, three-head regular zero.

Builds the Jacobian first over Fraction, then reduces modulo a checked prime.
Uses ordinary Python integer elimination, not the NumPy search implementation.
"""
from fractions import Fraction as Q
import json
from math import isqrt
from pathlib import Path


def mod(value, prime):
    return value.numerator * pow(value.denominator, -1, prime) % prime


def eliminate(matrix, prime):
    a = [row[:] for row in matrix]
    ids = list(range(len(a)))
    pivots = []
    determinant = 1
    rank = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        if pivot != rank:
            a[pivot], a[rank] = a[rank], a[pivot]
            ids[pivot], ids[rank] = ids[rank], ids[pivot]
            determinant = -determinant
        pivots.append(ids[rank])
        value = a[rank][col]
        determinant = determinant * value % prime
        inverse = pow(value, -1, prime)
        for i in range(rank + 1, len(a)):
            multiplier = a[i][col] * inverse % prime
            a[i] = [(v - multiplier * w) % prime for v, w in zip(a[i], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank, determinant % prime, pivots


def main():
    directory = Path(__file__).parent
    cert = json.loads((directory / 'integer-zero-fiber-16.json').read_text())
    n, heads, prime = cert['n'], cert['heads'], cert['prime']
    assert (n, heads) == (16, 3)
    assert all(prime % k for k in range(2, isqrt(prime) + 1))
    b = cert['denominator_slopes']
    u = [[Q(v, cert['numerator_scale']) for v in row]
         for row in cert['numerator_scaled_slopes']]
    assert all(v > 0 for row in b for v in row)
    vertices = cert['sample_indices']
    assert len(vertices) == len(set(vertices)) == 2 * n * heads
    assert set(cert['parameter_columns']) == set(range(2 * n * heads))
    rational_jacobian = []
    clone_rows, clone_vertices = [], []
    for vertex in vertices:
        assert 0 < vertex < 1 << n
        x = [(vertex >> i) & 1 for i in range(n)]
        d = [Q(1 + sum(b[h][i] * x[i] for i in range(n))) for h in range(heads)]
        a = [sum(u[h][i] * x[i] for i in range(n)) for h in range(heads)]
        assert all(v > 0 for v in d)
        assert 1 + sum(a[h] / d[h] for h in range(heads)) == 0
        row = [Q(x[i]) / d[h] for h in range(heads) for i in range(n)]
        row += [-Q(x[i]) * a[h] / d[h] ** 2 for h in range(heads) for i in range(n)]
        rational_jacobian.append(row)
        if x[0] == 1:
            clone_vertices.append(vertex)
            clone_rows.append([mod(Q(1) / v, prime) for v in d]
                              + [mod(-v / w ** 2, prime) for v, w in zip(a, d)])
    matrix = [[mod(v, prime) for v in row] for row in rational_jacobian]
    rank, determinant, _ = eliminate(matrix, prime)
    assert rank == 96 and determinant != 0
    clone_rank, _, selected = eliminate(clone_rows, prime)
    assert clone_rank == 6
    clone_matrix = [clone_rows[i] for i in selected]
    clone_rank, clone_determinant, _ = eliminate(clone_matrix, prime)
    assert clone_rank == 6 and clone_determinant != 0
    report = dict(status='PASS', prime=prime, jacobian_size=96,
                  determinant_mod_prime=determinant,
                  clone_coordinate=0,
                  clone_sample_vertices=[clone_vertices[i] for i in selected],
                  clone_determinant_mod_prime=clone_determinant,
                  rational_zero_scores_checked=len(vertices),
                  scope='regular coordinate zero fiber; no asymptotic head lower bound')
    (directory / 'integer-zero-fiber-verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
