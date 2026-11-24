#!/usr/bin/env python3
"""Exact finite check of eventual affine-minor stability, not universality."""
import itertools
import json
from pathlib import Path
import sympy as sp

s = sp.symbols('s')
perms = tuple(itertools.permutations(range(3)))
tokens = (1, 2, 4)
exponent = 2
v = [1 / (1 - s * x) ** exponent for x in tokens]
# All orbit points have a common coordinate sum. The first two
# coordinates together with 1 therefore give full affine coordinates.
mat = sp.Matrix([[1, v[pi[0]], v[pi[1]]] for pi in perms])
records = []
delta = sp.Rational(1, 8)
identically_zero = 0
for k in (1, 2, 3):
    for rows in itertools.combinations(range(6), k):
        for cols in itertools.combinations(range(3), k):
            det = sp.factor(mat.extract(rows, cols).det())
            if det == 0:
                identically_zero += 1
                continue
            numerator, denominator = sp.fraction(det)
            poly = sp.Poly(numerator, s)
            valuation = min(m[0] for m, coefficient in poly.terms())
            low = poly.nth(valuation)
            tail = sum(abs(coefficient) for (degree,), coefficient in poly.terms()
                       if degree > valuation)
            if tail:
                delta = min(delta, abs(low) / (2 * tail))
            records.append((det, numerator, denominator, valuation))
assert delta > 0
sample_checks = 0
for det, numerator, denominator, valuation in records:
    expected = None
    for divisor in (1, 2, 3, 5, 17):
        value = sp.cancel(det.subs(s, delta / divisor))
        assert value != 0
        sign = sp.sign(value)
        if expected is None:
            expected = sign
        assert sign == expected
        sample_checks += 1
# Exactly verify positivity of the original denominator factors throughout
# the selected interval. The numerator coefficient bound used above
# proves every nonzero minor has a fixed sign there, rather than merely
# comparing the five samples.
assert all(1 - delta * token > 0 for token in tokens)
result = {
    'status': 'exact finite affine-minor stability check; no asymptotic compiler claim',
    'H': 3,
    'pole_tokens': tokens,
    'kernel_exponent': exponent,
    'orbit_points': len(perms),
    'nonzero_minors': len(records),
    'identically_zero_minors': identically_zero,
    'positive_interval_endpoint': str(delta),
    'rational_sample_checks': sample_checks,
}
path = Path(__file__).with_suffix('.json')
path.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
