"""Independent exact arithmetic audit of the four-denominator counterexample."""
from fractions import Fraction as Q
from itertools import combinations
import json


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def scale(a, q):
    return (a[0] * q, a[1] * q)


def product(values):
    result = 1
    for value in values:
        result *= value
    return result


def main():
    slopes = [(10, 10, 1, 1), (1, 1, 10, 10), (10, 1, 10, 1), (1, 10, 1, 10)]
    bits = [tuple((v >> i) & 1 for i in range(4)) for v in range(16)]
    table = [product(1 + sum(bi * xi for bi, xi in zip(b, x)) for b in slopes) for x in bits]
    assert table == [1, 484, 484, 9072, 484, 9072, 20736, 81796,
                     484, 20736, 9072, 81796, 9072, 81796, 81796, 279841]
    t = (Q(1, 10), Q(1, 10000))
    w = (Q(-1252875804328031226236292, 16013505298103043438130897),
         Q(23924656286642536357360, 16013505298103043438130897))
    point = [(Q(0), Q(1)), t, t, w]
    assert all(z[1] > 0 for z in point)
    value = (Q(0), Q(0))
    for coefficient, x in zip(table, bits):
        term = (Q(coefficient), Q(0))
        for i, xi in enumerate(x):
            if xi:
                term = mul(term, point[i])
        value = add(value, term)
    assert value == (0, 0)
    weights = [Q(coefficient, 10 ** sum(x)) for coefficient, x in zip(table, bits)]
    partition = sum(weights)
    moments = [sum(weight * x[i] for weight, x in zip(weights, bits)) for i in range(4)]
    pair = sum(weight * x[0] * x[3] for weight, x in zip(weights, bits))
    assert partition == Q(13273681, 10000)
    assert pair * partition - moments[0] * moments[3] == Q(1231117189, 50000)
    covariance = pair / partition - moments[0] * moments[3] / partition ** 2
    assert covariance == Q(2462234378000, 176190607289761) > 0
    rayleigh = 100 * (moments[0] * moments[3] - pair * partition)
    assert rayleigh == Q(-1231117189, 500)
    print(json.dumps({'status': 'PASS', 'table': table, 'complex_zero_exact': True,
                      'all_imaginary_parts_positive': True,
                      'covariance': str(covariance), 'rayleigh_difference': str(rayleigh)}))


if __name__ == '__main__':
    main()
