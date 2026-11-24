"""Finite exact checks for the written fixed-unit-basis one-head construction."""
from itertools import product

for n in range(2, 8):
    m, k = n // 2, n - n // 2
    inputs = tuple(product((0, 1), repeat=n))
    tables = set()
    for r in product(range(2 ** m), repeat=k):
        table = []
        for bits in inputs:
            x, z = bits[:m], bits[m:]
            address = sum((2 ** j) * x[j] for j in range(m))
            # All expressions are scaled by k+1, including alpha.
            den = k + 1 + sum((k + 1) * (4 * 2 ** j - 2) * x[j] for j in range(m))
            den += sum((4 * (k + 1) * r[i] + 1) * z[i] for i in range(k))
            num = sum(2 * (k + 1) * (4 * 2 ** j - 1) * x[j] for j in range(m))
            p = num - den
            expected = (k + 1) * (-1 + 4 * address - 4 * sum(r[i] * z[i] for i in range(k))) - sum(z)
            assert den > 0 and p == expected and p != 0
            if sum(bits) <= 1:
                assert p == (1 if sum(x) == 1 else -1) * den
            table.append(p > 0)
        tables.add(tuple(table))
    expected_count = 2 ** (m * k)
    assert len(tables) == expected_count
    print(f'n={n}, m={m}, k={k}, fixed unit-level basis, distinct strict tables={len(tables)}=2^{m*k}')
