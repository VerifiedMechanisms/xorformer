"""Exact finite checks of the written Boolean-normal-form obstruction."""
from itertools import combinations
from math import factorial
import json


def surjections(n, k):
    # Inclusion-exclusion, with the integer convention 0**positive = 0.
    from math import comb
    return sum((-1) ** (k-j) * comb(k,j) * j**n for j in range(k+1))


def check(n):
    masks = range(1 << n)
    coeff = {s: surjections(n, s.bit_count()) for s in masks}
    assert coeff[0] == 0
    assert coeff[(1 << n)-1] == factorial(n)
    for x in masks:
        value = sum(c for s,c in coeff.items() if s & x == s)
        assert value == x.bit_count()**n
    half = [s for s in masks if s.bit_count() == n//2]
    full = (1 << n)-1
    nonzeros = 0
    for s in half:
        row = []
        for t in half:
            # Derivatives using no z0 see only the full squarefree monomial.
            entry = factorial(n) if s & t == 0 and s | t == full else 0
            if entry:
                row.append(t)
                nonzeros += 1
        assert row == [full ^ s]
    return dict(n=n, source_length=n+1, target_length_lower=2**n,
                middle_catalecticant_rank_lower=len(half),
                nonzero_matrix_entries=nonzeros, boolean_points=2**n)


if __name__ == '__main__':
    print(json.dumps([check(n) for n in range(2,11,2)], indent=2))
