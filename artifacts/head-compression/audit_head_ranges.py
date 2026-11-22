#!/usr/bin/env python3
"""Exact ranges of affine fractions and a certified cancellation ratio.

For an affine numerator and a denominator positive on a Boolean cube,
the extrema occur among sorted coefficient-ratio prefixes. Each returned
extremum is independently checked by maximizing an affine difference.
No numerical optimizer or search module is imported.
"""
import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import random
import sys

sys.set_int_max_str_digits(0)


def exact_extreme(a, b, maximize=True):
    """Return the exact extremum and an attaining original cube vertex."""
    n = len(a) - 1
    assert len(b) == n + 1
    assert b[0] + sum(min(0, v) for v in b[1:]) > 0
    aa, bb = list(a), list(b)
    complemented = [v < 0 for v in b[1:]]
    for i, flip in enumerate(complemented, 1):
        if flip:
            aa[0] += aa[i]
            bb[0] += bb[i]
            aa[i] = -aa[i]
            bb[i] = -bb[i]
    point = [0] * n
    for i in range(1, n + 1):
        if bb[i] == 0 and (aa[i] > 0 if maximize else aa[i] < 0):
            point[i - 1] = 1
    av = aa[0] + sum(v * u for v, u in zip(aa[1:], point))
    bv = bb[0]
    best = Fraction(av, bv)
    witness = point.copy()
    order = sorted((i for i in range(1, n + 1) if bb[i] > 0),
                   key=lambda i: Fraction(aa[i], bb[i]), reverse=maximize)
    for i in order:
        point[i - 1] = 1
        av += aa[i]
        bv += bb[i]
        value = Fraction(av, bv)
        if (value > best if maximize else value < best):
            best, witness = value, point.copy()
    witness = [1 - v if flip else v
               for v, flip in zip(witness, complemented)]
    # Independent affine certificate: q A - p B has the required sign.
    diff = [best.denominator * ai - best.numerator * bi
            for ai, bi in zip(a, b)]
    if maximize:
        assert diff[0] + sum(max(0, v) for v in diff[1:]) == 0
    else:
        assert diff[0] + sum(min(0, v) for v in diff[1:]) == 0
    assert diff[0] + sum(v * u for v, u in zip(diff[1:], witness)) == 0
    return best, witness


def as_pair(value):
    return [value.numerator, value.denominator]


def self_test():
    rng = random.Random(20261122)
    cases = 0
    for n in range(0, 9):
        for _ in range(100):
            a = [rng.randrange(-30, 31) for _ in range(n + 1)]
            slopes = [rng.randrange(-20, 21) for _ in range(n)]
            b = [1 + rng.randrange(20) - sum(min(0, v) for v in slopes)] + slopes
            values = [Fraction(a[0] + sum(v * u for v, u in zip(a[1:], x)),
                               b[0] + sum(v * u for v, u in zip(b[1:], x)))
                      for x in itertools.product((0, 1), repeat=n)]
            assert exact_extreme(a, b, False)[0] == min(values)
            assert exact_extreme(a, b, True)[0] == max(values)
            cases += 1
    return {"exact_random_checks": cases, "dimensions": list(range(9)),
            "mixed_and_zero_slopes_allowed": True,
            "independent_affine_optimality_certificates_checked": True}


def audit(certificate, margin_audit, bits=256):
    data = json.loads(certificate.read_text())
    report = json.loads(margin_audit.read_text())
    digest = hashlib.sha256(certificate.read_bytes()).hexdigest()
    assert report['input_sha256'] == digest
    assert report['all_target_signs_certified']
    assert report['whole_cube_denominator_admissibility']
    assert bits > 0
    scale = 1 << bits
    lower = upper = 0
    records = []
    for h in data['heads']:
        lo, xlo = exact_extreme(h['numerator'], h['denominator'], False)
        hi, xhi = exact_extreme(h['numerator'], h['denominator'], True)
        half = (hi - lo) / 2
        floor = (half.numerator * scale) // half.denominator
        ceil = -((-half.numerator * scale) // half.denominator)
        lower += floor
        upper += ceil
        records.append({'minimum': as_pair(lo), 'maximum': as_pair(hi),
                        'minimum_vertex': xlo, 'maximum_vertex': xhi})
    ml, mu = report['minimum_margin_interval_numerators']
    md = report['interval_denominator']
    assert ml > 0
    ratio_lo = Fraction(lower * md, scale * mu)
    ratio_hi = Fraction(upper * md, scale * ml)
    return {'input_sha256': digest, 'n': data['n'], 'heads': len(records),
            'head_extrema': records,
            'total_half_range_interval': [lower, upper, scale],
            'range_to_margin_lower': as_pair(ratio_lo),
            'range_to_margin_upper': as_pair(ratio_hi),
            'range_to_margin_approximation': float(ratio_hi),
            'independent_affine_optimality_certificates_checked': True,
            'scope': 'This supplied score only; no universal upper or lower head bound.'}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate', nargs='?', type=Path)
    p.add_argument('margin_audit', nargs='?', type=Path)
    p.add_argument('--self-test', action='store_true')
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    if args.self_test:
        result = self_test()
    else:
        assert args.certificate is not None and args.margin_audit is not None
        result = audit(args.certificate, args.margin_audit)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('head_extrema', 'total_half_range_interval',
                                   'range_to_margin_lower', 'range_to_margin_upper')}))
