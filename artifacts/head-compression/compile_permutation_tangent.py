#!/usr/bin/env python3
"""Compile a checked rational ideal first variation to actual rational heads.

Implements the explicit epsilon bound in weighted-root-completion.tex.
The score certificate must still be checked by audit_rational_score.py,
which imports none of this construction code.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

from search_permutation_tangent_smt import affine, verify


def multiply(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def compile_witness(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    source_audit = verify(data)
    n, m = data['n'], len(data['u'])
    roots = data['u'] + data['v']
    perturb = [[Fraction(t) for t in row] for row in data['a'] + data['b']]
    signs = [-1] * m + [1] * m
    coefficient_bound = max(Fraction(1), *(abs(t) for row in perturb for t in row))
    minimum_first = None
    maximum_tail = Fraction(0)
    firsts = []
    for index in range(1 << n):
        bits = [(index >> i) & 1 for i in range(n)]
        c = 1 + m * sum(bits)
        factors = [[Fraction(c + affine(row, bits)), affine(delta, bits)]
                   for row, delta in zip(roots, perturb)]
        q = [Fraction(0)] * (2*m)
        for h, sign in enumerate(signs):
            term = [Fraction(sign)]
            for g, factor in enumerate(factors):
                if g != h:
                    term = multiply(term, factor)
            q = [a+b for a,b in zip(q, term)]
        assert q[0] == 0
        assert (-1)**sum(bits) * q[1] > 0
        firsts.append(str(q[1]))
        minimum_first = abs(q[1]) if minimum_first is None else min(minimum_first, abs(q[1]))
        maximum_tail = max(maximum_tail, sum(abs(t) for t in q[2:]))
    epsilon = min(Fraction(1, 2), 1/(2*coefficient_bound),
                  minimum_first/(4*(maximum_tail+1)))
    assert epsilon > 0
    heads = []
    for row, delta, sign in zip(roots, perturb, signs):
        denominator = [Fraction(t) + epsilon*d + (1 if i == 0 else m)
                       for i, (t, d) in enumerate(zip(row, delta))]
        assert min(denominator) >= Fraction(1, 2)
        scale = math.lcm(*(t.denominator for t in denominator))
        heads.append({'numerator': [sign*scale] + [0]*n,
                      'denominator': [int(t*scale) for t in denominator]})
    return {'n': n, 'labels': [(-1)**i.bit_count() for i in range(1 << n)],
            'heads': heads, 'bias': [0, 1],
            'scope': 'This finite parity table only. No improvement on known parity complexity and no universal bound.',
            'construction': {'source_sha256': hashlib.sha256(raw).hexdigest(),
                             'source_audit': source_audit,
                             'epsilon': str(epsilon),
                             'perturbation_coefficient_bound': str(coefficient_bound),
                             'minimum_first_coefficient': str(minimum_first),
                             'maximum_tail_coefficient_sum': str(maximum_tail),
                             'first_coefficients': firsts}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('witness', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    result = compile_witness(args.witness)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'n':result['n'], 'heads':len(result['heads']),
                      'epsilon':result['construction']['epsilon'],
                      'scope':result['scope']}))


if __name__ == '__main__':
    main()
