"""Exact numerator-norm dual vector at the regular Boolean zero fiber.

The square Jacobian has 96 rows and 96 columns. Exact fraction-free elimination
also gives explicit signs, while two modular checks independently verify that
every dual coordinate is nonzero. Run via heavy on the shared machine.
"""
from fractions import Fraction as Q
import json
from math import prod, isqrt
from pathlib import Path
import time


def solve_exact(matrix, target):
    a = [list(row) + [v] for row, v in zip(matrix, target)]
    n = len(a)
    previous = 1
    for k in range(n - 1):
        pivot = next(i for i in range(k, n) if a[i][k])
        a[k], a[pivot] = a[pivot], a[k]
        diagonal = a[k][k]
        for i in range(k + 1, n):
            left = a[i][k]
            for j in range(k + 1, n + 1):
                numerator = diagonal * a[i][j] - left * a[k][j]
                a[i][j], remainder = divmod(numerator, previous)
                assert remainder == 0
            a[i][k] = 0
        previous = diagonal
    assert a[-1][-2]
    answer = [Q(0)] * n
    for i in reversed(range(n)):
        answer[i] = (Q(a[i][-1]) - sum(a[i][j] * answer[j]
                     for j in range(i + 1, n))) / a[i][i]
    assert all(sum(row[j] * answer[j] for j in range(n)) == value
               for row, value in zip(matrix, target))
    return answer


def solve_mod(matrix, target, p):
    assert all(p % d for d in range(2, isqrt(p) + 1))
    a = [[v % p for v in row] + [t % p] for row, t in zip(matrix, target)]
    n = len(a)
    det = 1
    for k in range(n):
        pivot = next(i for i in range(k, n) if a[i][k])
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            det = -det
        det = det * a[k][k] % p
        inverse = pow(a[k][k], -1, p)
        a[k] = [v * inverse % p for v in a[k]]
        for i in range(n):
            if i != k:
                scale = a[i][k]
                a[i] = [(v - scale * w) % p for v, w in zip(a[i], a[k])]
    answer = [row[-1] for row in a]
    assert det
    assert all(answer)
    assert all(sum(row[j] * answer[j] for j in range(n)) % p == value % p
               for row, value in zip(matrix, target))
    return det, answer


def main():
    started = time.monotonic()
    root = Path(__file__).parent
    data = json.loads((root / 'integer-zero-fiber-16.json').read_text())
    n, h = data['n'], data['heads']
    u, b = data['numerator_scaled_slopes'], data['denominator_slopes']
    scale = data['numerator_scale']
    assert (n, h, scale) == (16, 3, 3)
    rows, denominators, scales = [], [], []
    for vertex in data['sample_indices']:
        bits = [(vertex >> i) & 1 for i in range(n)]
        den = [1 + sum(b[k][i] * bits[i] for i in range(n)) for k in range(h)]
        num = [sum(u[k][i] * bits[i] for i in range(n)) for k in range(h)]
        assert 1 + sum(Q(num[k], scale * den[k]) for k in range(h)) == 0
        row_scale = scale * prod(d * d for d in den)
        row = [row_scale * bits[i] // den[k] for k in range(h) for i in range(n)]
        row += [-num[k] * bits[i] * (row_scale // (scale * den[k]**2))
                for k in range(h) for i in range(n)]
        rows.append(row)
        scales.append(row_scale)
        denominators.append(den)
    m = len(rows)
    assert m == 2 * n * h
    transpose = [[rows[j][i] for j in range(m)] for i in range(m)]
    gradient_int = [2 * u[k][i] for k in range(h) for i in range(n)] + [0] * (n * h)
    modular = []
    for prime in (101, 65521):
        det, answer = solve_mod(transpose, gradient_int, prime)
        modular.append({'prime': prime, 'cleared_determinant': det,
                        'solution': answer, 'nonzero_coordinates': m})
    w = solve_exact(transpose, gradient_int)
    dual = [Q(scales[i], scale) * w[i] for i in range(m)]
    assert all(dual)
    labels = [1 if v > 0 else -1 for v in dual]
    # Independently use the original rational derivatives to check J^T v = grad g.
    for k in range(h):
        for i in range(n):
            direct_u, direct_b = Q(0), Q(0)
            for r, vertex in enumerate(data['sample_indices']):
                bit = (vertex >> i) & 1
                den = denominators[r][k]
                num = sum(u[k][j] * ((vertex >> j) & 1) for j in range(n))
                direct_u += dual[r] * Q(bit, den)
                direct_b -= dual[r] * Q(bit * num, scale * den**2)
            assert direct_u == Q(2 * u[k][i], scale)
            assert direct_b == 0
    report = {'status': 'PASS', 'n': n, 'heads': h, 'samples': m,
              'gradient': 'squared numerator norm, with constant score fixed at one',
              'dual': list(map(str, dual)), 'labels': labels,
              'positive_labels': labels.count(1), 'negative_labels': labels.count(-1),
              'min_abs_dual': str(min(map(abs, dual))), 'modular': modular,
              'elapsed_seconds': time.monotonic() - started,
              'main_target_proved': False,
              'analytic_scope': 'equal small margins and strict local minima on the selected constraints only'}
    (root / 'zero-fiber-dual-checks.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in ('dual', 'modular', 'labels', 'min_abs_dual')}))


if __name__ == '__main__':
    main()
