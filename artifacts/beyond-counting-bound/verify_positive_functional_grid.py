"""Independent exact arithmetic checks for the positive functional grid.

This verifies an obstruction to arbitrary linear-section bounds. Every score
is positive, so it is not a head-complexity lower-bound certificate.
"""
from fractions import Fraction as F
from itertools import product
import json
import math
from pathlib import Path

import sympy as sp


def main():
    q, d, k, heads = 3, 3, 3, 2
    m = 2 * q + 1
    t = sp.Symbol('t')
    p = sp.prod(t-r for r in range(1, q+1))
    den = sp.prod(t+j for j in range(1, m+1))
    residues = [F(int(p.subs(t, -j)) ** 2,
                  math.prod(ell-j for ell in range(1, m+1) if ell != j))
                for j in range(1, m+1)]
    expression = sum(sp.Rational(a.numerator, a.denominator)/(t+j)
                     for j, a in enumerate(residues, 1))
    assert sp.cancel(expression - p*p/den) == 0
    second = [sp.cancel(sp.diff(expression, t, 2).subs(t, r))
              for r in range(1, q+1)]
    assert all(v > 0 for v in second)
    count = 0
    for flat in product(range(1, q+1), repeat=heads*k):
        parameters = [flat[h*k:(h+1)*k] for h in range(heads)]
        functional = F(0)
        for i in range(k):
            for j, weight in enumerate(residues, 1):
                address = [(j-1) >> a & 1 for a in range(d)]
                selector = [int(a == i) for a in range(k)]
                score = F(0)
                for row in parameters:
                    denominator = (1 + sum(a*b for a, b in zip(row, selector))
                                   + sum((1 << a)*bit for a, bit in enumerate(address)))
                    assert denominator == row[i] + j
                    assert denominator > 0
                    score += F(1, denominator)
                assert score > 0
                functional += weight*score
        assert functional == 0
        count += 1
    assert count == q ** (heads*k)
    result = dict(q=q, address_bits=d, selector_bits=k, input_bits=d+k, heads=heads,
                  grid_points=count, head_permutation_orbits=math.comb(q**k+heads-1, heads),
                  residues=[str(v) for v in residues],
                  second_derivatives_at_roots=[str(v) for v in second],
                  polynomial_identity='PASS', full_grid_functional_identity='PASS',
                  boolean_pattern='constant true',
                  scope='Auxiliary linear-section obstruction, not a lower bound on W(n).')
    output = Path(__file__).with_name('positive-functional-grid-verification.json')
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
