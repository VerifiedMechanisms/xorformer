"""Independent exact full-cube verification of a rescaled arithmetic fiber.

Enumerates in Gray-code order using Python integers. This does not use the
vectorized search, floating point, or a nonlinear optimizer. Run with heavy.
"""
import hashlib
import json
from fractions import Fraction
from math import prod, lcm
from pathlib import Path

from verify_integer_binary_fiber import inverse_mod


def main():
    root = Path(__file__).parent
    data = json.loads((root / 'integer-binary-fiber-18.json').read_text())
    n, h = data['n'], data['heads']
    weights, u = data['denominator_slopes'], data['numerator_scaled_slopes']
    assert (n, h, data['numerator_scale']) == (18, 3, 3)
    descent = json.loads((root / 'rescaled-binary-descent.json').read_text())
    direction = [Fraction(z) for z in descent['direction']]
    common = lcm(*(z.denominator for z in direction))
    direction_integer = [[int(common * direction[j * n + i]) for i in range(n)] for j in range(h)]
    assert len(direction) == n * h and all(abs(z) <= 1 for z in direction)
    dot = sum(u[j][i] * direction[j * n + i] for j in range(h) for i in range(n))
    assert dot == Fraction(descent['integer_numerator_dot_direction']) < -1
    epsilon = Fraction(descent['epsilon'])
    assert epsilon.numerator == 1
    norm_difference = 2 * 23100 * epsilon * dot + epsilon ** 2 * sum(z*z for z in direction)
    assert norm_difference < 0
    den, num = [1] * h, [0] * h
    direction_num = [0] * h
    previous = 0
    zeros, negative_active = [], []
    minimum_gap = None
    count_negative = 0
    for k in range(1 << n):
        v = k ^ (k >> 1)
        if k:
            changed = (v ^ previous).bit_length() - 1
            step = 1 if (v >> changed) & 1 else -1
            for j in range(h):
                den[j] += step * weights[j][changed]
                num[j] += step * u[j][changed]
                direction_num[j] += step * direction_integer[j][changed]
        previous = v
        assert all(b > 0 for b in den)
        denominator = 3 * prod(den)
        numerator = sum(num[j] * prod(den[t] for t in range(h) if t != j) for j in range(h))
        label = 1 if numerator >= 0 else -1
        assert label * (denominator + 69300 * numerator) >= denominator
        direction_p = sum(direction_num[j] * prod(den[t] for t in range(h) if t != j) for j in range(h))
        perturbed_denominator = common * epsilon.denominator * prod(den)
        perturbed_numerator = perturbed_denominator + 23100 * common * epsilon.denominator * numerator + direction_p
        assert label * perturbed_numerator >= perturbed_denominator
        if numerator == 0:
            zeros.append(v)
        if numerator < 0:
            count_negative += 1
            gap = Fraction(-numerator, denominator)
            minimum_gap = gap if minimum_gap is None else min(minimum_gap, gap)
            if gap == Fraction(1, 34650):
                negative_active.append(v)
    assert minimum_gap == Fraction(1, 34650)
    assert negative_active == [92746]
    assert len(zeros) == 128
    samples = data['sample_indices'].copy()
    samples[53] = 92746
    matrix = []
    for r, v in enumerate(samples):
        x = [(v >> i) & 1 for i in range(n)]
        b = [1 + sum(weights[j][i] * x[i] for i in range(n)) for j in range(h)]
        a = [sum(u[j][i] * x[i] for i in range(n)) for j in range(h)]
        raw = sum(Fraction(a[j], 3 * b[j]) for j in range(h))
        assert 1 + 69300 * raw == (-1 if r == 53 else 1)
        row = [3 * x[i] * b[j] * prod(b[t] ** 2 for t in range(h) if t != j)
               for j in range(h) for i in range(n)]
        row += [-a[j] * x[i] * prod(b[t] ** 2 for t in range(h) if t != j)
                for j in range(h) for i in range(n)]
        matrix.append(row)
    assert len(set(samples)) == 108
    modular = []
    for prime in (101, 65537):
        determinant, _ = inverse_mod(matrix, prime)
        assert determinant != 0
        modular.append(dict(prime=prime, determinant=determinant))
    old = json.loads((root / 'integer-binary-fiber-matrices.json').read_text())
    coefficients = [sum(matrix[53][j] * old['inverse_mod_101'][j][k] for j in range(108)) % 101
                    for k in range(108)]
    assert coefficients[53] != 0
    assert all(sum(coefficients[k] * old['cleared_jacobian'][k][j] for k in range(108)) % 101 == matrix[53][j] % 101
               for j in range(108))
    report = dict(status='PASS', vertices_checked=1 << n, zero_layer_size=len(zeros),
                  negative_labels=count_negative, minimum_gap=str(minimum_gap), scale=69300,
                  negative_active_vertices=negative_active, selected_active_count=108,
                  determinants=modular, replacement_coefficients_mod_101=coefficients,
                  replacement_coefficient_53=coefficients[53],
                  strict_numerator_descent_verified=True,
                  descent_epsilon=str(epsilon), norm_difference=str(norm_difference),
                  source_sha256=hashlib.sha256((root / 'integer-binary-fiber-18.json').read_bytes()).hexdigest(),
                  canonical_minimum_certified=False, main_target_proved=False)
    (root / 'rescaled-binary-unit-checks.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'replacement_coefficients_mod_101'}))


if __name__ == '__main__':
    main()
