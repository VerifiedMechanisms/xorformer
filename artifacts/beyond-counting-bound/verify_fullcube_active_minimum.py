"""Exact full-cube compatibility for the binary active-minimum construction.

Enumerates all vertices with an incremental Gray-code calculation, independently
of the matrix-product exploration. Then checks all first-order margins exactly.
The nonlinear existence assertion follows by the written inverse-function proof.
Run via heavy on the shared machine.
"""
from fractions import Fraction as Q
import hashlib
import json
from math import prod
from pathlib import Path
import time

from verify_zero_fiber_dual import solve_exact


def main():
    started = time.monotonic()
    root = Path(__file__).parent
    data = json.loads((root / 'integer-zero-fiber-16.json').read_text())
    dual = json.loads((root / 'zero-fiber-dual-checks.json').read_text())
    n, h = data['n'], data['heads']
    b, u = data['denominator_slopes'], data['numerator_scaled_slopes']
    scale = data['numerator_scale']
    assert (n, h, scale) == (16, 3, 3)
    labels = [0] * (2**n)
    zeros = []
    min_nonzero = None
    den, num = [1] * h, [0] * h
    last = 0
    for step in range(2**n):
        vertex = step ^ (step >> 1)
        if step:
            changed = vertex ^ last
            coordinate = changed.bit_length() - 1
            sign = 1 if vertex & changed else -1
            for k in range(h):
                den[k] += sign * b[k][coordinate]
                num[k] += sign * u[k][coordinate]
        last = vertex
        assert all(d > 0 for d in den)
        numerator = scale * prod(den) + sum(num[k] * prod(den[j]
                     for j in range(h) if j != k) for k in range(h))
        if numerator:
            labels[vertex] = 1 if numerator > 0 else -1
            margin = Q(abs(numerator), scale * prod(den))
            min_nonzero = margin if min_nonzero is None else min(min_nonzero, margin)
        else:
            zeros.append(vertex)
    zeros.sort()
    samples = data['sample_indices']
    assert len(samples) == 96 and len(set(samples)) == 96
    assert set(samples) <= set(zeros)
    assert len(zeros) == 106

    def row(vertex):
        bits = [(vertex >> i) & 1 for i in range(n)]
        d = [1 + sum(b[k][i] * bits[i] for i in range(n)) for k in range(h)]
        a = [sum(u[k][i] * bits[i] for i in range(n)) for k in range(h)]
        values = [Q(bits[i], d[k]) for k in range(h) for i in range(n)]
        values += [Q(-bits[i] * a[k], scale * d[k]**2)
                   for k in range(h) for i in range(n)]
        return values, scale * prod(v * v for v in d)

    matrix, target = [], []
    for vertex, label in zip(samples, dual['labels']):
        r, denominator = row(vertex)
        matrix.append([int(v * denominator) for v in r])
        target.append(label * denominator)
        labels[vertex] = label
    delta = solve_exact(matrix, target)
    for vertex, label in zip(samples, dual['labels']):
        r, _ = row(vertex)
        assert sum(a * d for a, d in zip(r, delta)) == label
    extra = []
    for vertex in sorted(set(zeros) - set(samples)):
        r, _ = row(vertex)
        value = sum(a * d for a, d in zip(r, delta))
        assert abs(value) > 14
        labels[vertex] = 1 if value > 0 else -1
        extra.append({'vertex': vertex, 'derivative': str(value),
                      'label': labels[vertex]})
    assert all(labels)
    truth_bytes = bytes(sum((labels[8*j+i] > 0) << i for i in range(8))
                        for j in range(2**n // 8))
    report = {'status': 'PASS', 'n': n, 'heads': h, 'all_vertices_checked': 2**n,
        'zero_vertices': zeros, 'selected_active_vertices': samples,
        'selected_labels': dual['labels'], 'extra_zero_derivatives': extra,
        'minimum_nonzero_base_score_abs': str(min_nonzero),
        'tangent_direction': list(map(str, delta)),
        'positive_truth_table_entries': labels.count(1),
        'truth_table_hex_little_endian_bits': truth_bytes.hex(),
        'truth_table_sha256': hashlib.sha256(truth_bytes).hexdigest(),
        'elapsed_seconds': time.monotonic() - started,
        'analytic_scope': 'full-cube strict local minima for every sufficiently small positive margin',
        'main_target_proved': False}
    (root / 'fullcube-active-minimum-checks.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k in
        ['status', 'all_vertices_checked', 'minimum_nonzero_base_score_abs',
         'positive_truth_table_entries', 'truth_table_sha256', 'elapsed_seconds', 'main_target_proved']}))


if __name__ == '__main__':
    main()
