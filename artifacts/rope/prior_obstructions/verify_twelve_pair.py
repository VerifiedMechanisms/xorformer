#!/usr/bin/env python3
"""Check the twelve-bit four-head certificate with Python integer arithmetic.

Certificate and checker adapted from VerifiedMechanisms/xorformer-runs commit
1899d884da3affbf21a8528bcb74b409c9783876. The new pure three-head lower bound is
symbolic, proved in Results/PureRoPEThreeHeadObstruction.lean.
"""
import itertools
import json
from fractions import Fraction
from pathlib import Path


def score(bits):
    z = [1 - 2*b for b in bits]
    return 22 + 20 * sum(z[2*i]*z[2*i+1] for i in range(6)) - sum(z)**2


def main():
    data = json.loads(Path(__file__).with_name('twelve_pair_four_heads.json').read_text())
    denominators, numerators = data['denominators'], data['numerators']
    assert len(denominators) == len(numerators) == 4
    assert all(len(row) == 13 for row in denominators + numerators)
    assert all(all(a < 0 for a in row[1:]) for row in denominators)
    pure = json.loads(Path(__file__).with_name('twelve_pair_pure_four_heads.json').read_text())
    assert len(pure['heads']) == 4
    for atom, ns, ds in zip(pure['heads'], numerators, denominators):
        a = list(map(Fraction, atom['a']))
        b = list(map(Fraction, atom['b']))
        gamma, eta, v0, v1 = [Fraction(atom[key]) for key in ('gamma', 'eta', 'v0', 'v1')]
        assert len(a) == len(b) == 12 and min(a + b + [gamma]) > 0
        # Exact affine coefficients certify equality of the pure and vanilla
        # fractions, so the full-cube check below verifies both architectures.
        assert gamma + sum(a) == ds[0]
        assert [bi-ai for ai, bi in zip(a, b)] == ds[1:]
        assert eta + v0 * sum(a) == ns[0]
        assert [bi*v1-ai*v0 for ai, bi in zip(a, b)] == ns[1:]
    minima, margin = [10**100] * 4, 10**100
    for bits in itertools.product((0, 1), repeat=12):
        row = (1,) + bits
        ds = [sum(a*b for a, b in zip(d, row)) for d in denominators]
        ns = [sum(a*b for a, b in zip(n, row)) for n in numerators]
        assert min(ds) > 0
        minima = [min(a, b) for a, b in zip(minima, ds)]
        cleared = sum(ns[h] * ds[(h+1) % 4] * ds[(h+2) % 4] * ds[(h+3) % 4]
                      for h in range(4))
        q = score(bits)
        assert q != 0 and cleared != 0 and (q > 0) == (cleared > 0)
        margin = min(margin, abs(cleared))
        assert score(tuple(1-b for b in bits)) == q
    assert minima == data['minimum_denominators']
    assert margin == data['minimum_signed_cleared']
    zero = [0] * 12
    assert score(zero) == -2
    for j in range(6):
        single = zero.copy()
        single[2*j+1] = 1
        assert score(single) == 2
        for k in range(6):
            if j == k:
                continue
            double = single.copy()
            double[2*k+1] = 1
            assert score(double) == -2
            for a, b in itertools.product((0, 1), repeat=2):
                bits = zero.copy()
                bits[2*j], bits[2*k+1] = a, b
                assert (score(bits) > 0) == (a != b)
    print(f'4,096 exact classifications passed; denominator minima {minima}; '
          f'minimum absolute cleared score {margin}.')
    print('Four rational pure atoms match all numerator and denominator coefficients exactly.')


if __name__ == '__main__':
    main()
