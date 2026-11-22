#!/usr/bin/env python3
"""Check a sufficient exact certificate for merging two same-orientation heads.

Individual ranges center each head. Optimal projective rescaling minimizes
max |(D-B)/(D+B)|. Its comparison with the certified margin can be made
using rational inequalities alone. Failure of this bound is not evidence
that a pair cannot be merged after further changes.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys
from audit_head_ranges import exact_extreme, as_pair
from audit_rational_score import audit

sys.set_int_max_str_digits(0)


def orientation(b):
    return 1 if all(v > 0 for v in b[1:]) else -1 if all(v < 0 for v in b[1:]) else 0


def rational_scale(m, M):
    with localcontext() as ctx:
        ctx.prec = 120
        product = m * M
        value = (Decimal(product.numerator)/Decimal(product.denominator)).sqrt()
        return Fraction(1/value)


def integer_head(a, b):
    scale = math.lcm(*(v.denominator for v in a+b))
    return {'numerator': [int(v*scale) for v in a],
            'denominator': [int(v*scale) for v in b]}


def merge(data, i, j, centres, scale):
    h, k = data['heads'][i], data['heads'][j]
    a = [Fraction(v)-centres[i]*w for v, w in zip(h['numerator'], h['denominator'])]
    c = [scale*(Fraction(v)-centres[j]*w) for v, w in zip(k['numerator'], k['denominator'])]
    b = [Fraction(v)+scale*w for v, w in zip(h['denominator'], k['denominator'])]
    new_head = integer_head([2*(v+w) for v, w in zip(a, c)], b)
    bias = Fraction(*data['bias']) + centres[i] + centres[j]
    return {'n': data['n'], 'labels': data['labels'],
            'heads': [h for q, h in enumerate(data['heads']) if q not in (i, j)] + [new_head],
            'bias': as_pair(bias), 'scope': 'This fixed truth table only; no universal bound.',
            'merge': {'pair': [i, j], 'denominator_scale': as_pair(scale)}}


def run(certpath, auditpath, out):
    data = json.loads(certpath.read_text())
    margin_audit = json.loads(auditpath.read_text())
    digest = hashlib.sha256(certpath.read_bytes()).hexdigest()
    assert digest == margin_audit['input_sha256']
    assert margin_audit['all_target_signs_certified']
    assert margin_audit['whole_cube_denominator_admissibility']
    gamma = Fraction(margin_audit['minimum_margin_interval_numerators'][0],
                     margin_audit['interval_denominator'])
    heads = data['heads']
    ranges, centres = [], []
    for h in heads:
        lo = exact_extreme(h['numerator'], h['denominator'], False)[0]
        hi = exact_extreme(h['numerator'], h['denominator'], True)[0]
        ranges.append((hi-lo)/2)
        centres.append((hi+lo)/2)
    best, passed, checked = [], [], 0
    for i, h in enumerate(heads):
        for j in range(i+1, len(heads)):
            k = heads[j]
            if orientation(h['denominator'])*orientation(k['denominator']) < 0:
                continue
            m = exact_extreme(k['denominator'], h['denominator'], False)[0]
            M = exact_extreme(k['denominator'], h['denominator'], True)[0]
            R = ranges[i]+ranges[j]
            admissible = R <= gamma or M*(R-gamma)**2 < m*(R+gamma)**2
            # Floating values rank candidates only. The pass condition is exact.
            rho = math.tanh(math.log1p(float((M-m)/m))/4)
            cost = float(R)*rho
            item = {'pair': [i, j], 'optimal_bound_approximation': cost,
                    'ratio_minimum': as_pair(m), 'ratio_maximum': as_pair(M),
                    'sum_half_ranges': as_pair(R), 'exact_sufficient_test_passed': admissible}
            checked += 1
            best.append(item)
            best.sort(key=lambda z: z['optimal_bound_approximation'])
            best = best[:10]
            if admissible:
                scale = rational_scale(m, M)
                rho_exact = max(abs(scale*m-1)/(scale*m+1), abs(scale*M-1)/(scale*M+1))
                if rho_exact*R < gamma:
                    candidate = merge(data, i, j, centres, scale)
                    path = out/f'merged-{i}-{j}.json'
                    path.write_text(json.dumps(candidate)+'\n')
                    report = audit(path, 224)
                    assert report['all_target_signs_certified']
                    (out/f'merged-{i}-{j}-audit.json').write_text(json.dumps(report, indent=2)+'\n')
                    passed.append({'pair': [i, j], 'certificate': path.name,
                                   'error_upper_bound': as_pair(rho_exact*R)})
    result = {'input_sha256': digest, 'n': data['n'], 'heads': len(heads),
              'compatible_pairs_checked': checked,
              'certified_merges': passed, 'best_sufficient_bounds': best,
              'scope': 'A sufficient bound for these pairs only; failure is not an impossibility result.'}
    (out/'result.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'pairs_checked': checked, 'certified_merges': len(passed),
                      'best_bound_approximation': best[0]['optimal_bound_approximation'] if best else None}))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate', type=Path)
    p.add_argument('audit', type=Path)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    run(args.certificate, args.audit, args.out)
