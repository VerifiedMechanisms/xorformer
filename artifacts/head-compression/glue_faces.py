#!/usr/bin/env python3
"""Glue a positive-slope lower-face score to a mixed-slope upper-face score.

All arithmetic and margin tests are rational or integer. The input scores
must be strict certificates with nonconstant, strictly oriented denominators.
This operation preserves a finite truth table; it is not a compressed
construction for arbitrary dimensions. Use heavy for large certificates.
"""
import argparse
from fractions import Fraction as Q
import json
from math import lcm
from pathlib import Path


def margin_bound(data, threshold=Q(0)):
    n, heads, labels = data['n'], data['heads'], data['labels']
    assert len(labels) == 1 << n and all(y in (-1, 1) for y in labels)
    assert heads
    for head in heads:
        a, b = head['numerator'], head['denominator']
        assert len(a) == len(b) == n + 1
        assert all(isinstance(v, int) for v in a + b)
        assert all(v > 0 for v in b[1:]) or all(v < 0 for v in b[1:])
        assert b[0] + sum(min(v, 0) for v in b[1:]) > 0
    bias = Q(*data['bias'])
    precision = 160
    while precision <= 16384:
        scale = 1 << precision
        least = None
        for vertex, label in enumerate(labels):
            indices = [i + 1 for i in range(n) if vertex >> i & 1]
            lo = (scale * bias.numerator) // bias.denominator
            for head in heads:
                a, b = head['numerator'], head['denominator']
                av = a[0] + sum(a[i] for i in indices)
                bv = b[0] + sum(b[i] for i in indices)
                lo += (scale * av) // bv
            hi = lo + len(heads) + 1
            signed_lower = lo if label == 1 else -hi
            signed_upper = hi if label == 1 else -lo
            assert signed_upper > scale * threshold, ('Insufficient input margin', vertex)
            if signed_lower <= scale * threshold:
                break
            least = signed_lower if least is None else min(least, signed_lower)
        else:
            return Q(least, scale)
        precision *= 2
    raise ValueError('Unable to certify a strict input margin at the precision limit')


def normalized_heads(data, margin):
    result = []
    for head in data['heads']:
        scale = head['denominator'][0]
        a = [Q(v, scale) for v in head['numerator']]
        b = [Q(v, scale) for v in head['denominator']]
        result.append([a, b])
    bias = Q(*data['bias'])
    result[0][0] = [a + bias * b for a, b in zip(*result[0])]
    for head in result:
        head[0] = [a / margin for a in head[0]]
    return result


def ceil(value):
    return -((-value.numerator) // value.denominator)


def integral_head(a, b):
    scale = lcm(*(v.denominator for v in a + b))
    return {'numerator': [int(v * scale) for v in a],
            'denominator': [int(v * scale) for v in b]}


def glue(lower, upper):
    assert lower['n'] == upper['n']
    assert all(all(v > 0 for v in h['denominator'][1:]) for h in lower['heads'])
    m0, m1 = margin_bound(lower), margin_bound(upper)
    h0, h1 = normalized_heads(lower, m0), normalized_heads(upper, m1)
    a0 = sum(sum(abs(v) for v in a) for a, b in h0)
    minima = [b[0] + sum(min(v, 0) for v in b[1:]) for a, b in h1]
    s1 = sum(sum(abs(v) for v in a) / bmin for (a, b), bmin in zip(h1, minima))
    d1 = sum(sum(abs(v) for v in a) / bmin**2 for (a, b), bmin in zip(h1, minima))
    bound = max(1, ceil(a0), ceil(s1), ceil(d1))
    amplitude = bound + 1
    foreground_slope = 4 * amplitude * (bound + 1)
    background_slope = min(min(minima) / 2, Q(1, 8 * (bound + 1)))
    heads = []
    for a, b in h0:
        heads.append(integral_head([amplitude * v for v in a] + [Q(0)],
                                   b + [Q(foreground_slope)]))
    for a, b in h1:
        orientation = 1 if b[1] > 0 else -1
        heads.append(integral_head(a + [Q(0)], b + [orientation * background_slope]))
    result = {'n': lower['n'] + 1, 'labels': lower['labels'] + upper['labels'],
              'heads': heads, 'bias': [0, 1],
              'scope': 'This glued finite truth table only; not a universal upper bound.',
              'construction': {'kind': 'positive lower face and mixed upper face',
                               'lower_input_margin': str(m0), 'upper_input_margin': str(m1),
                               'bound': bound, 'foreground_slope': foreground_slope,
                               'background_slope': str(background_slope),
                               'proved_margin_lower_bound': '1/2'}}
    certified_margin = margin_bound(result, Q(1, 2))
    assert certified_margin > Q(1, 2)
    result['construction']['checked_margin_lower_bound'] = str(certified_margin)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('lower', type=Path)
    parser.add_argument('upper', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    result = glue(json.loads(args.lower.read_text()), json.loads(args.upper.read_text()))
    args.out.write_text(json.dumps(result) + '\n')
    print(json.dumps({'n': result['n'], 'heads': len(result['heads']),
                      'construction': result['construction']}))
