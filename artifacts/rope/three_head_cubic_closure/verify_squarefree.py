"""Exact six-group cubic certificate; no Boolean separation is asserted."""
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path


def verify():
    path = Path(__file__).with_name("squarefree_certificate.json")
    record = json.loads(path.read_text())
    denominators = [[Fraction(x) for x in row] for row in record["B"]]
    numerators = [[Fraction(x) for x in row] for row in record["U"]]
    assert all(x > 0 for row in denominators for x in row)
    for triple in combinations(range(6), 3):
        coefficient = Fraction(0)
        for head in range(3):
            other_heads = [h for h in range(3) if h != head]
            j, k = other_heads
            for coordinate in triple:
                a, b = [i for i in triple if i != coordinate]
                coefficient += numerators[head][coordinate] * (
                    denominators[j][a] * denominators[k][b]
                    + denominators[j][b] * denominators[k][a]
                )
        expected = Fraction(0)
        if len({i // 2 for i in triple}) == 3:
            expected = Fraction((-1) ** sum(i % 2 == 0 for i in triple))
        assert coefficient == expected, (triple, coefficient, expected)
    print("Verified all 20 squarefree cubic coefficients and 18 positive denominator entries.")


if __name__ == "__main__":
    verify()
