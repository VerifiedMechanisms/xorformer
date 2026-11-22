"""Independent exact arithmetic audit of the three-bit product branches.

Uses only the Python standard library. The general classification and the
complex generic-degree argument are written proofs, not finite inferences.
"""
from fractions import Fraction as Q
import json
from pathlib import Path


def determinant(matrix):
    a = [[Q(v) for v in row] for row in matrix]
    result = Q(1)
    for k in range(len(a)):
        pivot = next((i for i in range(k, len(a)) if a[i][k]), None)
        if pivot is None:
            return Q(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            result = -result
        value = a[k][k]
        result *= value
        for i in range(k + 1, len(a)):
            ratio = a[i][k] / value
            for j in range(k + 1, len(a)):
                a[i][j] -= ratio * a[k][j]
            a[i][k] = 0
    return result


def jacobian(a, b):
    n = len(a)
    rows = []
    for i in range(n):
        row = [Q(0)] * (2 * n)
        row[i] = 1 + b[i]
        row[n + i] = 1 + a[i]
        rows.append(row)
    for i in range(n):
        for j in range(i + 1, n):
            row = [Q(0)] * (2 * n)
            row[i], row[j] = b[j], b[i]
            row[n + i], row[n + j] = a[j], a[i]
            rows.append(row)
    return rows


def table(a, b):
    return [(1 + sum(a[i] for i in range(3) if (v >> i) & 1)) *
            (1 + sum(b[i] for i in range(3) if (v >> i) & 1))
            for v in range(8)]


def main():
    report = {'status': 'PASS', 'branches': []}
    baseline = table([Q(2)] * 3, [Q(3)] * 3)
    for k in range(4):
        a, b = [Q(2)] * 3, [Q(3)] * 3
        if k:
            a[k - 1], b[k - 1] = Q(5, 3), Q(7, 2)
        assert all(v > 0 for v in a + b)
        assert table(a, b) == baseline
        det = determinant(jacobian(a, b))
        assert det == (Q(2) if k == 0 else Q(-23, 3))
        report['branches'].append({'first_slopes': list(map(str, a)),
            'second_slopes': list(map(str, b)), 'determinant': str(det)})
    assert determinant(jacobian(list(map(Q, [1, 2, 3])),
                                list(map(Q, [4, 5, 7])))) == -24
    report['common_table'] = list(map(str, baseline))
    report['independent_dominance_determinant'] = -24
    report['generic_degree_proof'] = 'written, using reduced base points and multihomogeneous Bezout'
    report['main_target_proved'] = False
    output = Path(__file__).with_name('boolean-product-checks.json')
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
