#!/usr/bin/env python3
"""Check a sufficient exact certificate for merging two same-orientation heads.

Individual ranges center each head. Optimal projective rescaling minimizes
max |(D-B)/(D+B)|. Its comparison with the certified margin can be made
using rational inequalities alone. Failure of this bound is not evidence
that a pair cannot be merged after further changes.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys
from audit_head_ranges import exact_extreme, as_pair
from audit_rational_score import audit
from verify_certificate import verify

sys.set_int_max_str_digits(0)


def orientation(b):
    return 1 if all(v > 0 for v in b[1:]) else -1 if all(v < 0 for v in b[1:]) else 0


def strict_merge_scale(m, M, R, gamma):
    """Choose an exactly rational point in the strict feasible interval."""
    assert 0 < m <= M and gamma > 0 and R >= 0
    if m == M:
        return 1/m
    if R <= gamma:
        return Fraction(1)
    lower = (R-gamma)/(m*(R+gamma))
    upper = (R+gamma)/(M*(R-gamma))
    assert 0 < lower < upper
    return (lower+upper)/2


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
                scale = strict_merge_scale(m, M, R, gamma)
                rho_exact = max(abs(scale*m-1)/(scale*m+1), abs(scale*M-1)/(scale*M+1))
                assert rho_exact*R < gamma
                candidate = merge(data, i, j, centres, scale)
                path = out/f'merged-{i}-{j}.json'
                path.write_text(json.dumps(candidate)+'\n')
                gap = gamma-rho_exact*R
                interval_width = len(candidate['heads'])+1
                bits = max(224, (gap.denominator*interval_width).bit_length()
                           - gap.numerator.bit_length()+2)
                assert (1 << bits)*gap.numerator > interval_width*gap.denominator
                report = audit(path, bits)
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


def self_test(out):
    records = []
    for perturbation in (0, 1, 1000):
        directory = out/str(perturbation)
        directory.mkdir(parents=True, exist_ok=True)
        heads = [
            {'numerator': [-13, 2, 7, 5, 11], 'denominator': [10, 1, 2, 3, 4]},
            {'numerator': [3000000, -4000000, 6000000, -2000000, 5000000],
             'denominator': [10000000, 1000000+perturbation, 2000000, 3000000, 4000000]}]
        labels = []
        for vertex in range(16):
            indices = [i+1 for i in range(4) if (vertex >> i) & 1]
            score = Fraction(1, 7)+sum((Fraction(
                h['numerator'][0]+sum(h['numerator'][i] for i in indices),
                h['denominator'][0]+sum(h['denominator'][i] for i in indices))
                for h in heads), Fraction(0))
            assert score != 0
            labels.append(1 if score > 0 else -1)
        assert len(set(labels)) == 2
        source = directory/'source.json'
        source.write_text(json.dumps({'n': 4, 'labels': labels, 'heads': heads,
                                      'bias': [1, 7]})+'\n')
        source_audit = directory/'source-audit.json'
        source_audit.write_text(json.dumps(audit(source, 224))+'\n')
        run(source, source_audit, directory)
        result = json.loads((directory/'result.json').read_text())
        assert len(result['certified_merges']) == 1
        check = verify(directory/'merged-0-1.json')
        assert check['heads'] == 1
        records.append({'perturbation': perturbation, 'integer_audit_passed': True,
                        'independent_fraction_audit': check})
    result = {'checks': records, 'scope': 'End-to-end implementation checks only.'}
    (out/'self-test.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'end_to_end_checks_passed': len(records)}))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate', nargs='?', type=Path)
    p.add_argument('audit', nargs='?', type=Path)
    p.add_argument('--self-test', action='store_true')
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.self_test:
        self_test(args.out)
    else:
        assert args.certificate is not None and args.audit is not None
        run(args.certificate, args.audit, args.out)
