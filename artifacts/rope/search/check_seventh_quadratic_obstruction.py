"""Verify an exact degree-two moment obstruction at replication seven.

The six simultaneous permutations of each aggregate pattern have equal
moments through degree two and opposite source signs. Independent averaging
inside each group of 21 Boolean coordinates preserves polynomial degree.
Consequently this aggregate certificate also rules out every quadratic
threshold representation on the original 126-bit cube.
"""

from fractions import Fraction
import itertools
import json
from pathlib import Path


def orbit(a, b):
    return [tuple(a[i] for i in p)+tuple(b[i] for i in p)
            for p in itertools.permutations(range(3))]


def score(v):
    a, b = v[:3], v[3:]
    total = sum(a)+sum(b)
    return sum(Fraction(2*(total+a[i]), 1400+a[i]-b[i]) for i in range(3))


def verify():
    positive = orbit((-21, 9, 19), (9, 1, -19))
    negative = orbit((-21, 9, 19), (13, -15, -7))
    assert len(positive) == len(negative) == 6
    for j in range(6):
        assert sum(v[j] for v in positive) == sum(v[j] for v in negative)
        for k in range(6):
            assert sum(v[j]*v[k] for v in positive) == sum(v[j]*v[k] for v in negative)
    assert all(score(v) == Fraction(3637, 346730560) for v in positive)
    assert all(score(v) == -Fraction(203, 346729048) for v in negative)
    assert all(-21 <= x <= 21 and x % 2 for v in positive+negative for x in v)
    return {'replicas': 7, 'positive_aggregate_numerators': positive,
            'negative_aggregate_numerators': negative,
            'positive_score': '3637/346730560', 'negative_score': '-203/346729048',
            'first_and_second_moments_equal': True,
            'scope': 'Threshold degree at least three on the original 126-bit Boolean cube'}


if __name__ == '__main__':
    result = verify()
    print(json.dumps(result, indent=2))
    Path('artifacts/rope/search/seventh_replication_quadratic_obstruction.exact.json').write_text(
        json.dumps(result, indent=2)+'\n')
