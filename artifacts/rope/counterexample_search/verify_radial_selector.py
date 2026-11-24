"""Exact vanilla-three certificate for a near-miss local-pattern function.

Only Python's standard library is used.  The function is
sign(t * ((sum(X)-sum(Y))**2 - 169)) on seventeen spins.
This is an upper certificate, not a pure-versus-vanilla separation.
"""
from itertools import product
import json
from pathlib import Path


def certificate():
    # Affine coefficients are [constant, selector, X_0,...,X_7,Y_0,...,Y_7].
    r = [1000] + [20] * 17
    l = [0, 0] + [1] * 8 + [-1] * 8
    t = [0, 1] + [0] * 16
    add = lambda a, b: [x + y for x, y in zip(a, b)]
    scale = lambda c, a: [c * x for x in a]
    return {
        'n': 17,
        'coordinate_order': 'selector t, eight X spins, eight Y spins',
        'function': 'sign(t*((sum(X)-sum(Y))^2-169))',
        'denominators': [r, add(r, add(l, scale(-13, t))),
                         add(r, add(l, scale(13, t)))],
        'numerators': [scale(26, t), add(scale(-1, l), scale(-13, t)),
                       add(l, scale(-13, t))],
        'cleared_identity': 'sum_h N_h*product_(j!=h) D_j = 26*t*(L^2-169*t^2)',
        'threshold_degree': 3,
        'vanilla_heads': 3,
        'pure_head_claim': None,
    }


def verify(record):
    den, num = record['denominators'], record['numerators']
    assert all(len(d) == 18 and d[0] > sum(abs(x) for x in d[1:])
               and min(d[1:]) > 0 for d in den)
    minimum = None
    positive = 0
    for z in product([-1, 1], repeat=17):
        affine = (1,) + z
        d = [sum(a * b for a, b in zip(row, affine)) for row in den]
        n = [sum(a * b for a, b in zip(row, affine)) for row in num]
        assert min(d) > 0
        cleared = sum(n[h] * d[(h + 1) % 3] * d[(h + 2) % 3]
                      for h in range(3))
        t, l = z[0], sum(z[1:9]) - sum(z[9:17])
        desired = t * (l * l - 169)
        assert cleared == 26 * desired and desired != 0
        positive += desired > 0
        minimum = min(minimum, abs(cleared)) if minimum is not None else abs(cleared)
    # A degree-two sign polynomial, averaged to be odd in t and even in all
    # spatial spins together, becomes t times a constant.  The target has
    # both spatial signs, explicitly at L=16 and L=0, so this is impossible.
    assert 16 * 16 - 169 > 0 and 0 * 0 - 169 < 0
    return {'vertices': 2 ** 17, 'positive_labels': positive,
            'minimum_absolute_cleared_score': minimum,
            'denominator_cube_lower_bounds':
            [d[0] - sum(abs(x) for x in d[1:]) for d in den]}


if __name__ == '__main__':
    path = Path(__file__).with_name('exact_radial_selector.json')
    record = json.loads(path.read_text())
    assert record == certificate()
    print(json.dumps(verify(record), sort_keys=True))
