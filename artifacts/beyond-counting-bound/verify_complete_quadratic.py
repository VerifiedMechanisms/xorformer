#!/usr/bin/env python3
"""Exact finite checks for the complete-quadratic Fourier obstruction."""
import json
from pathlib import Path


def fwht(values):
    result = list(values)
    step = 1
    while step < len(result):
        for start in range(0, len(result), 2 * step):
            for j in range(start, start + step):
                a, b = result[j], result[j + step]
                result[j], result[j + step] = a + b, a - b
        step *= 2
    return result


records = []
for n in range(2, 13, 2):
    m = n // 2
    values = [(-1) ** (x.bit_count() * (x.bit_count() - 1) // 2)
              for x in range(1 << n)]
    spectrum = fwht(values)
    assert {abs(x) for x in spectrum} == {1 << m}
    for w in range(n + 1):
        polynomial = (-1) ** m
        for j in range(1, m + 1):
            polynomial *= 2 * w - 4 * j + 1
        assert polynomial != 0
        assert (polynomial > 0) == (w % 4 < 2)
    changes = sum((w % 4 < 2) != ((w + 1) % 4 < 2) for w in range(n))
    assert changes == m
    if n <= 8:
        correlation = [sum(values[x] * values[x ^ a] for x in range(1 << n))
                       for a in range(1 << n)]
        assert correlation == [1 << n] + [0] * ((1 << n) - 1)
    records.append({"n": n, "head_count_from_profile": m,
                    "walsh_absolute_value": 1 << m,
                    "strict_fourier_support_lower_bound": 1 << m,
                    "direct_autocorrelation_checked": n <= 8})

destination = Path(__file__).with_name("complete-quadratic-checks.json")
destination.write_text(json.dumps({"arithmetic": "exact Python integers",
                                  "instances": records}, indent=2) + "\n")
print(f"Verified {len(records)} even dimensions, 2 through 12.")
