"""Finite exact checks for the written permutation moment congruence.

These checks do not prove an unrestricted head-complexity lower bound.
"""

from fractions import Fraction
from math import comb
import hashlib
import json
from pathlib import Path


def partitions(total, largest=None):
    if total == 0:
        yield ()
        return
    if largest is None:
        largest = total
    for first in range(min(largest, total), 0, -1):
        for rest in partitions(total - first, first):
            yield (first,) + rest


def coefficient_for_row(k, occupancy, j, heads):
    return sum(
        Fraction(comb(occupancy, left) * comb(k - occupancy, j - left))
        * Fraction(heads - 1, heads) ** left
        * Fraction(-1, heads) ** (j - left)
        for left in range(max(0, j - (k - occupancy)), min(j, occupancy) + 1)
    )


def valuation(value, prime):
    result = 0
    while value % prime == 0:
        result += 1
        value //= prime
    return result


def main():
    identity_checks = 0
    nonvanishing_checks = 0
    for k in range(2, 15):
        heads = 1 << (k * (k - 1)).bit_length()
        for occupancy in partitions(k):
            assert len(occupancy) <= heads
            for j in range(2, k + 1):
                direct = sum(coefficient_for_row(k, count, j, heads) for count in occupancy)
                direct += (heads - len(occupancy)) * coefficient_for_row(k, 0, j, heads)
                integer = (-1) ** j * (1 - j) * comb(k, j)
                for degree in range(2, j + 1):
                    moment = sum(comb(count, degree) for count in occupancy if count >= degree)
                    integer += (-1) ** (j - degree) * heads ** (degree - 1) * moment * comb(k - degree, j - degree)
                assert direct * heads ** (j - 1) == integer
                assert integer % heads == ((-1) ** j * (1 - j) * comb(k, j)) % heads
                identity_checks += 1
                assert integer != 0
                assert abs(direct) >= Fraction(1, heads ** (j - 1))
                nonvanishing_checks += 1

    valuation_checks = 0
    for prime in (2, 3, 5, 7):
        for k in range(2, 257):
            bound = 0
            power = prime
            while power <= k:
                bound += 1
                power *= prime
            for j in range(2, k + 1):
                assert valuation(comb(k, j), prime) <= bound
                valuation_checks += 1

    root = Path(__file__).resolve().parent
    report = {
        "scope": "Finite exact arithmetic only; no asymptotic head lower bound",
        "occupancy_max_k": 14,
        "identity_checks": identity_checks,
        "nonvanishing_checks": nonvanishing_checks,
        "valuation_checks": valuation_checks,
        "valuation_max_k": 256,
        "primes": [2, 3, 5, 7],
        "files": {
            name: hashlib.sha256((root / name).read_bytes()).hexdigest()
            for name in ("permutation-moment-divisibility.md", Path(__file__).name)
        },
    }
    (root / "permutation-moment-divisibility-audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
