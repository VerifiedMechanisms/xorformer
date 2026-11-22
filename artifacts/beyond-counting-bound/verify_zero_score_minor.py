"""Exact certificate against a proposed nH zero-score Jacobian rank bound.

Only Python integer and Fraction arithmetic is used for the certificate.
The optional numerical derivative check audits the experimental search code.
"""
from fractions import Fraction as Q
import json
from pathlib import Path


def determinant(matrix):
    a = [row[:] for row in matrix]
    result = Q(1)
    for i in range(len(a)):
        pivot = next((j for j in range(i, len(a)) if a[j][i]), None)
        if pivot is None:
            return Q(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            result = -result
        value = a[i][i]
        result *= value
        for j in range(i + 1, len(a)):
            ratio = a[j][i] / value
            for k in range(i + 1, len(a)):
                a[j][k] -= ratio * a[i][k]
    return result


def exact_certificate():
    b = [[Q(1, 7)] * 4, [Q(10, 71), Q(10, 71), Q(9, 71), Q(9, 71)]]
    u = [[Q(-568, 7), Q(-568, 7), Q(-71, 7), Q(-71, 7)],
         [Q(5670, 71), Q(5670, 71), Q(630, 71), Q(630, 71)]]
    indices = [1, 2, 4, 5, 6, 7, 8, 9, 13]
    columns = [0, 1, 2, 3, 4, 5, 6, 8, 10]
    rows = []
    for vertex in range(16):
        x = [(vertex >> i) & 1 for i in range(4)]
        d = [1 + sum(b[h][i] * x[i] for i in range(4)) for h in range(2)]
        a = [sum(u[h][i] * x[i] for i in range(4)) for h in range(2)]
        assert all(v > 0 for v in d)
        score = 1 + sum(a[h] / d[h] for h in range(2))
        l1, l2 = 1 - x[0] - x[1], 1 - x[2] - x[3]
        d_original = 7 + sum(x)
        expected = Q(497, 10) * l1 * l2 / (d_original * (d_original + Q(1, 10) * l2))
        assert score == expected
        if vertex in indices:
            assert score == 0
            row = [Q(x[i]) / d[h] for h in range(2) for i in range(4)]
            row += [-Q(x[i]) * a[h] / d[h] ** 2 for h in range(2) for i in range(4)]
            rows.append((vertex, [row[c] for c in columns]))
    assert [i for i, _ in rows] == indices
    det = determinant([row for _, row in rows])
    assert det == Q(10401023166874151, 15516104491008000000)
    assert det != 0
    assert all(v > 0 for head in b for v in head)
    return dict(status='PASS', input_bits=4, heads=2, sample_indices=indices,
                parameter_columns=columns, minor_determinant=str(det),
                conclusion='zero-score Jacobian rank is at least 9, exceeding nH=8')


def check_search_derivative():
    import numpy as np
    from search_zero_fibers import score_and_jacobian
    rng = np.random.default_rng(170129)
    worst = 0.0
    for n, heads in [(4, 2), (6, 3), (9, 5)]:
        x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
        orientation = (np.arange(heads) % 2).astype(float)
        v = np.r_[rng.normal(size=heads * n), rng.uniform(.1, 2, size=heads * n)]
        _, jac = score_and_jacobian(v, x, orientation, derivatives=True)
        step = 1e-5
        for j in range(len(v)):
            direction = np.zeros_like(v)
            direction[j] = step
            difference = (score_and_jacobian(v + direction, x, orientation)
                          - score_and_jacobian(v - direction, x, orientation)) / (2 * step)
            error = float(np.max(np.abs(difference - jac[:, j])))
            worst = max(worst, error)
    assert worst < 1e-8
    return dict(status='PASS', maximum_absolute_error=worst,
                scope='finite-difference audit only; not part of the exact theorem')


if __name__ == '__main__':
    report = dict(exact=exact_certificate(), numerical_derivative=check_search_derivative())
    target = Path(__file__).with_name('zero-score-minor-verification.json')
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))
