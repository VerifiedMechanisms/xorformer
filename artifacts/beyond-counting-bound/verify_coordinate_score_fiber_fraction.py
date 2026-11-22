"""Independent exact-Fraction audit of the coordinate-score fiber certificate.

This verifier does not import the interval verifier or its arithmetic class.
The analytic implication is the contraction argument in the accompanying note.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path


def values_and_jacobian(z, rows, n, h):
    values, jacobian, data = [], [], []
    for mask in rows:
        active = [i for i in range(n) if mask >> i & 1]
        nums = [sum(z[i * h + j] for i in active) for j in range(h)]
        dens = [1 + sum(z[n * h + i * h + j] for i in active)
                for j in range(h)]
        assert min(dens) > 0
        values.append(1 + sum(a / b for a, b in zip(nums, dens)))
        jacobian.append([1 / dens[j] if i in active else Q(0)
                         for i in range(n) for j in range(h)] +
                        [-nums[j] / dens[j] ** 2 if i in active else Q(0)
                         for i in range(n) for j in range(h)])
        data.append((len(active), nums, dens))
    return values, jacobian, data


def determinant_mod(matrix, prime):
    a = [[int(v.numerator) * pow(int(v.denominator), -1, prime) % prime
          for v in row] for row in matrix]
    result = 1
    for j in range(len(a)):
        pivot = next(i for i in range(j, len(a)) if a[i][j])
        if pivot != j:
            a[pivot], a[j] = a[j], a[pivot]
            result = -result
        value = a[j][j]
        result = result * value % prime
        for i in range(j + 1, len(a)):
            c = a[i][j] * pow(value, -1, prime) % prime
            for k in range(j, len(a)):
                a[i][k] = (a[i][k] - c * a[j][k]) % prime
    return result


def verify(d):
    n, h = d['n'], d['heads']
    size = 2 * n * h
    rows = d['sample']
    assert len(rows) == size == len(set(rows))
    center = [Q(v, 2 ** d['center_bits']) for v in d['center_integer']]
    inverse = [[Q(v, 2 ** d['inverse_bits']) for v in row]
               for row in d['inverse_integer']]
    assert len(center) == len(inverse) == size
    assert all(len(row) == size for row in inverse)
    radius = Q(1, 2 ** d['radius_bits'])
    assert all(b > radius for b in center[n * h:])
    base = [Q(v, d['numerator_scale'])
            for row in d['numerator_integer'] for v in row]
    base += [Q(v, d['denominator_scale'])
             for row in d['denominator_integer'] for v in row]
    assert all(b > 0 for b in base[n * h:])
    value, jac, data = values_and_jacobian(center, rows, n, h)
    target, base_jac, _ = values_and_jacobian(base, rows, n, h)
    residual = [x - y for x, y in zip(value, target)]
    eta = max(abs(sum(a * f for a, f in zip(row, residual))) for row in inverse)
    inverse_norm = max(sum(map(abs, row)) for row in inverse)
    defect = max(sum(abs(Q(i == j) - sum(inverse[i][k] * jac[k][j]
                                       for k in range(size)))
                     for j in range(size)) for i in range(size))
    variation = Q(0)
    for k, nums, dens in data:
        delta = k * radius
        row_bound = Q(0)
        for u, b in zip(nums, dens):
            lo = b - delta
            assert lo > 0
            numerator_derivative = delta / (b * lo)
            denominator_derivative = delta / lo ** 2 + (
                abs(u) * delta * (2 * b + delta) / (lo ** 2 * b ** 2))
            row_bound += k * (numerator_derivative + denominator_derivative)
        variation = max(variation, row_bound)
    contraction = defect + inverse_norm * variation
    assert eta < Q(1, 2 ** 200)
    assert contraction < Q(1, 2 ** 80)
    assert contraction < 1 and eta + contraction * radius < radius
    # A different prime from the integer-interval verifier.
    prime = 65537
    assert all(prime % k for k in range(2, 257))
    determinant = determinant_mod(base_jac, prime)
    assert determinant != 0
    old, _, _ = values_and_jacobian(base, range(2 ** n), n, h)
    _, _, all_data = values_and_jacobian(center, range(2 ** n), n, h)
    threshold = Q(283, 1024)
    differing = []
    for mask, (k, nums, dens) in enumerate(all_data):
        delta = k * radius
        lower, upper = Q(1), Q(1)
        for u, b in zip(nums, dens):
            assert b > delta
            corners = [a / c for a in (u - delta, u + delta)
                       for c in (b - delta, b + delta)]
            lower += min(corners)
            upper += max(corners)
        assert lower > threshold or upper < threshold
        assert old[mask] != threshold
        if (lower > threshold) != (old[mask] > threshold):
            differing.append(mask)
    assert differing == [39]
    return {'status': 'PASS_EXACT_FRACTION_CONTRACTION',
            'equations': size, 'n': n, 'heads': h,
            'eta_strict_upper_power_of_two': -200,
            'contraction_strict_upper_power_of_two': -80,
            'invariant_ball_checked': True,
            'base_jacobian_prime': prime,
            'base_jacobian_determinant_mod': determinant,
            'common_threshold': [threshold.numerator, threshold.denominator],
            'all_labels_strict': True, 'differing_vertices': differing,
            'arithmetic': 'fractions.Fraction; no interval code imported',
            'scope': 'certificate inequalities; analytic implication in written proof'}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('certificate', type=Path)
    p.add_argument('--output', required=True, type=Path)
    args = p.parse_args()
    result = verify(json.loads(args.certificate.read_text()))
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
