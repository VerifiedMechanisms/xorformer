"""Exact checks for the bounded-atom parity identities, not universality tests."""

from fractions import Fraction as Q
from itertools import product


def check(n, b0, b):
    vertices = list(product((0, 1), repeat=n))
    i0 = sum(
        (Q((-1) ** sum(x), b0 + sum(b[j] * x[j] for j in range(n))) for x in vertices),
        Q(0),
    )
    ii = [
        sum(
            (
                Q((-1) ** (sum(x) - 1), b0 + sum(b[j] * x[j] for j in range(n)))
                for x in vertices
                if x[i]
            ),
            Q(0),
        )
        for i in range(n)
    ]
    assert i0 >= 0 and all(t >= 0 for t in ii)
    assert sum(b[i] * ii[i] for i in range(n)) == b0 * i0
    assert all(i0 + t <= Q(1, b0) for t in ii)
    # These numerators range over an explicitly bounded affine family:
    # A = B - 2 b0 x_h - 2 sum_j b_j x_j.
    for h in range(n):
        a0 = b0
        a = [-v - (2 * b0 if j == h else 0) for j, v in enumerate(b)]
        values = []
        for x in vertices:
            value = Q(a0 + sum(a[j] * x[j] for j in range(n)),
                      b0 + sum(b[j] * x[j] for j in range(n)))
            assert -1 <= value <= 1
            values.append(value)
        parity_sum = sum(((-1) ** sum(x) * v for x, v in zip(vertices, values)), Q(0))
        assert parity_sum == a0 * i0 - sum(a[j] * ii[j] for j in range(n))
        assert abs(parity_sum) <= 2


checks = 0
for n in range(1, 7):
    for b0 in (1, 3):
        for b in ([0] * n, list(range(n)), list(range(1, n + 1)), [100] * n):
            check(n, b0, b)
            checks += 1
print(f"PASS: {checks} denominator configurations; exact identities, positivity, and correlation bound")
