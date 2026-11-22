#!/usr/bin/env python3
"""Independently verify a fixed-residual one-head noncompletion witness.

Uses integers and Fraction only, and imports no optimizer. This says nothing
about changing the retained heads or the universal head count.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)


def residual_interval(data, omitted, vertex, bits):
    scale = 1 << bits
    lower = 0
    width = 0
    terms = [data['bias']]
    active = [i + 1 for i in range(data['n']) if vertex >> i & 1]
    for index, head in enumerate(data['heads']):
        if index in omitted:
            continue
        a, b = head['numerator'], head['denominator']
        terms.append([a[0] + sum(a[i] for i in active),
                      b[0] + sum(b[i] for i in active)])
    for numerator, denominator in terms:
        assert denominator > 0
        q, remainder = divmod(numerator * scale, denominator)
        lower += q
        width += int(remainder != 0)
    return Fraction(lower, scale), Fraction(lower + width, scale)


def verify(source, witness, bits=224):
    data = json.loads(source.read_text())
    cert = json.loads(witness.read_text())
    assert hashlib.sha256(source.read_bytes()).hexdigest() == cert['source_sha256']
    n = data['n']
    omitted = set(cert['omitted_heads'])
    assert all(0 <= i < len(data['heads']) for i in omitted)
    orientation = cert['orientation']
    assert orientation in (1, -1)
    moments = [Fraction(0) for _ in range(n + 1)]
    upper = [Fraction(0) for _ in range(n + 1)]
    mass = Fraction(0)
    seen = set()
    for item in cert['weights']:
        vertex, weight = item['vertex'], Fraction(*item['weight'])
        assert 0 <= vertex < 1 << n and vertex not in seen
        seen.add(vertex)
        assert weight > 0
        mass += weight
        label = data['labels'][vertex]
        assert label in (-1, 1)
        z = [1] + [((vertex >> i) & 1) if orientation == 1
                   else 1 - ((vertex >> i) & 1) for i in range(n)]
        lo, hi = residual_interval(data, omitted, vertex, bits)
        for j, value in enumerate(z):
            factor = weight * label * value
            moments[j] += factor
            upper[j] += factor * (hi if factor >= 0 else lo)
    assert mass > 0 and all(value == 0 for value in moments)
    assert all(value <= 0 for value in upper)
    return {'verified': True, 'n': n, 'source_sha256': cert['source_sha256'],
            'omitted_heads': sorted(omitted), 'orientation': orientation,
            'support': len(seen), 'interval_bits': bits,
            'signed_affine_moments_exactly_zero': True,
            'residual_moment_upper_bounds': [[v.numerator, v.denominator] for v in upper],
            'scope': 'No one-head completion with this orientation of this fixed residual. '
                     'Retained heads cannot change; not an unrestricted lower bound.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('witness', type=Path)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    result = verify(args.source, args.witness)
    text = json.dumps(result, indent=2) + '\n'
    if args.out:
        args.out.write_text(text)
    else:
        print(text)
