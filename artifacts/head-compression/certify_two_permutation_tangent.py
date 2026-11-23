#!/usr/bin/env python3
"""Certify a specified zero-output tangent space over the reals.

This is not a universal head bound. A nonzero modular minor bounds the
rank of the real constraint matrix from below. An explicit integer
kernel basis, checked on the entire cube, gives the matching upper bound
and proves that every first variation has zero output for this pair.
Run with heavy. Requires python-flint and numpy.
"""
import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import random
import time

from flint import nmod_mat
import numpy as np

PRIME = 2147483647


def roots(x):
    n = len(x)
    return [sum(x)] + [k * (1 - x[k - 1]) + sum(x[k:])
                      for k in range(1, n + 1)]


def data(n, permutation, mask, vertex):
    x = [(vertex >> i) & 1 for i in range(n)]
    y = [x[permutation[i]] ^ ((mask >> i) & 1) for i in range(n)]
    u, v = roots(x), roots(y)
    return [1] + x, [u.index(j) for j in range(n + 1)], [v.index(j) for j in range(n + 1)]


def match_row(n, permutation, mask, vertex, root):
    m = n + 1
    z, iu, iv = data(n, permutation, mask, vertex)
    row = [0] * (2 * m * m)
    for i, bit in enumerate(z):
        row[m * iu[root] + i] += bit
        row[m * m + m * iv[root] + i] -= bit
    return row


def constraint_row(n, permutation, mask, index):
    vertex, j0 = divmod(index, n)
    j = j0 + 1
    dj = (-1) ** j * math.factorial(j) * math.factorial(n - j)
    d0 = math.factorial(n)
    a = match_row(n, permutation, mask, vertex, j)
    b = match_row(n, permutation, mask, vertex, 0)
    return [(dj * v - d0 * w) % PRIME for v, w in zip(a, b)]


def reconstruct(value):
    value = int(value)
    if not value:
        return Fraction(0)
    bound = math.isqrt(PRIME // 2)
    r0, r1, t0, t1 = PRIME, value, 0, 1
    while abs(r1) > bound:
        quotient = r0 // r1
        r0, r1 = r1, r0 - quotient * r1
        t0, t1 = t1, t0 - quotient * t1
    if t1 == 0:
        raise ValueError('rational reconstruction failed')
    answer = Fraction(r1, t1)
    if (abs(answer.numerator) > bound or answer.denominator > bound or
            (answer.numerator - value * answer.denominator) % PRIME):
        raise ValueError('rational reconstruction failed')
    return answer


def pivot_columns(matrix, rank):
    result = []
    start = 0
    for i in range(rank):
        for j in range(start, matrix.ncols()):
            if matrix[i, j]:
                result.append(j)
                start = j + 1
                break
        else:
            raise AssertionError('missing pivot')
    return result


def verify_basis(n, permutation, mask, basis):
    m = n + 1
    records = [data(n, permutation, mask, x) for x in range(1 << n)]
    z = np.array([r[0] for r in records], dtype=np.int64)
    iu = np.array([r[1] for r in records], dtype=np.int64)
    iv = np.array([r[2] for r in records], dtype=np.int64)
    vertices = np.arange(1 << n)[:, None]
    for column in basis:
        # The explicit bound makes every integer dot product and subtraction
        # below exact in int64, rather than a floating-point rank test.
        if 2 * m * max(map(abs, column), default=0) >= 2 ** 62:
            raise ValueError('basis exceeds the certified int64 range')
        coefficients = np.array(column, dtype=np.int64).reshape(2 * m, m)
        values = z @ coefficients.T
        difference = values[vertices, iu] - values[vertices, m + iv]
        if np.any(difference):
            raise ValueError('basis fails an exact full-cube matching equation')
    matrix = nmod_mat([[column[i] % PRIME for column in basis]
                      for i in range(2 * m * m)], PRIME)
    if matrix.rank() != len(basis):
        raise ValueError('basis is not independent modulo the prime')


def certify(n, permutation, mask, seed):
    started = time.monotonic()
    m, variables = n + 1, 2 * (n + 1) ** 2
    rng = random.Random(seed)
    match_indices = rng.sample(range((1 << n) * m), min((1 << n) * m, 8 * variables))
    match = [match_row(n, permutation, mask, *divmod(index, m)) for index in match_indices]
    nullspace, nullity = nmod_mat(match, PRIME).nullspace()
    basis = []
    for j in range(nullity):
        values = [reconstruct(nullspace[i, j]) for i in range(variables)]
        denominator = math.lcm(*(v.denominator for v in values))
        column = [v.numerator * (denominator // v.denominator) for v in values]
        divisor = math.gcd(*column)
        basis.append([v // divisor for v in column])
    verify_basis(n, permutation, mask, basis)

    indices = rng.sample(range((1 << n) * n), min((1 << n) * n, 8 * variables))
    rows = [constraint_row(n, permutation, mask, index) for index in indices]
    transposed, rank = nmod_mat(rows, PRIME).transpose().rref()
    selected = [indices[j] for j in pivot_columns(transposed, rank)]
    independent_rows = [constraint_row(n, permutation, mask, index) for index in selected]
    reduced, check_rank = nmod_mat(independent_rows, PRIME).rref()
    assert check_rank == rank
    columns = pivot_columns(reduced, rank)
    determinant = int(nmod_mat([[row[j] for j in columns] for row in independent_rows], PRIME).det())
    assert determinant != 0
    if rank + nullity != variables:
        raise ValueError('the sampled constraints do not certify zero output')
    return dict(n=n, permutation=permutation, complement_mask=mask, prime=PRIME,
                variables=variables, constraint_rank=rank, kernel_dimension=nullity,
                independent_constraint_indices=selected, minor_columns=columns,
                minor_determinant_mod_prime=determinant, integer_kernel_columns=basis,
                all_cube_matching_equations_checked=True,
                scope='This specified pair has zero real first-order output. No universal head bound.',
                seconds=time.monotonic() - started)


def verify(certificate):
    n = certificate['n']
    permutation = certificate['permutation']
    mask = certificate['complement_mask']
    assert certificate['prime'] == PRIME
    assert sorted(permutation) == list(range(n))
    assert 0 <= mask < 1 << n
    basis = certificate['integer_kernel_columns']
    assert all(len(v) == 2 * (n + 1) ** 2 for v in basis)
    verify_basis(n, permutation, mask, basis)
    indices = certificate['independent_constraint_indices']
    columns = certificate['minor_columns']
    rank = len(indices)
    assert len(set(indices)) == len(set(columns)) == rank == len(columns)
    assert all(0 <= i < (1 << n) * n for i in indices)
    assert all(0 <= i < 2 * (n + 1) ** 2 for i in columns)
    rows = [constraint_row(n, permutation, mask, index) for index in indices]
    determinant = int(nmod_mat([[row[j] for j in columns] for row in rows], PRIME).det())
    assert determinant != 0 and determinant == certificate['minor_determinant_mod_prime']
    assert rank + len(basis) == 2 * (n + 1) ** 2
    assert rank == certificate['constraint_rank']
    return dict(verified=True, n=n, real_constraint_rank=rank,
                real_kernel_dimension=len(basis), real_output_dimension=0,
                scope=certificate['scope'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--events', type=Path)
    parser.add_argument('--n', type=int, default=12)
    parser.add_argument('--trial', type=int, default=1)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--verify', type=Path)
    args = parser.parse_args()
    if args.verify:
        print(json.dumps(verify(json.loads(args.verify.read_text())), indent=2))
        return
    records = [json.loads(line) for line in args.events.read_text().splitlines()]
    event = next(e for e in records if e['n'] == args.n and e['trial'] == args.trial)
    certificate = certify(args.n, event['permutation'], event['complement_mask'],
                          2026112300 + args.n)
    args.out.write_text(json.dumps(certificate, indent=2) + '\n')
    print(json.dumps(verify(certificate), indent=2))


if __name__ == '__main__':
    main()
