"""Exact rational certificates for the local equal-weight split theorem."""

from fractions import Fraction as Q
from itertools import product
from math import comb, factorial
from flint import fmpq, fmpq_mat


def poly_mul(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def evaluate(a, t):
    out = Q(0)
    for x in reversed(a):
        out = out*t+x
    return out


def derivative(a):
    return [i*a[i] for i in range(1, len(a))] or [Q(0)]


def fq(x):
    return fmpq(x.numerator, x.denominator)


def rational(x):
    return Q(int(x.numerator), int(x.denominator))


def shift(a, t, length):
    return [sum((a[j]*comb(j, k)*t**(j-k)
                 for j in range(k, len(a))), Q(0))
            for k in range(length)]


def quotient_series(a, b, length):
    out = []
    for k in range(length):
        value = a[k] if k < len(a) else Q(0)
        value -= sum((b[i]*out[k-i]
                      for i in range(1, min(k+1, len(b)))), Q(0))
        out.append(value / b[0])
    return out


def power_sums(a, count):
    degree = len(a)-1
    assert a[-1] == 1
    out = [Q(degree)]
    for k in range(1, count+1):
        out.append(-sum((a[degree-j]*out[k-j]
                         for j in range(1, k)), Q(0))
                   - k*a[degree-k])
    return out


def check_degree(m):
    poles = [Q(i+1, 100*m) for i in range(m)]
    radius = Q(1, 400*m)
    endpoints = [p+sign*radius for p in poles for sign in (-1, 1)]
    polynomial = [Q(1)]
    for p in poles:
        polynomial = poly_mul(polynomial, [-p, Q(1)])
    dp = derivative(polynomial)
    point = Q(2)
    pseries = shift(polynomial, point, m+1)
    # Every prefix Wronskian, using Taylor coefficients to avoid numerical differentiation.
    columns = []
    for k in range(m):
        monomial = [Q(0)]*k+[Q(1)]
        series = quotient_series(shift(monomial, point, m+1), pseries, m+1)
        columns.append([factorial(j+1)*series[j+1] for j in range(m)])
    for q in range(1, m+1):
        matrix = fmpq_mat([[fq(columns[k][j]) for k in range(q)] for j in range(q)])
        rhs = ((-1)**q * factorial(q) * pseries[q]
               * product_factorials(q) / pseries[0]**(q+1))
        assert rational(matrix.det()) == rhs != 0

    checked = 0
    for q in range(1, m+1):
        queries = [Q(1)+Q(j+1, q+1) for j in range(q)]
        matrix = []
        for t in queries:
            pt, dpt = evaluate(polynomial, t), evaluate(dp, t)
            matrix.append([((k*t**(k-1)*pt if k else Q(0))-t**k*dpt)/pt**2
                           for k in range(q)])
        inverse = fmpq_mat([[fq(x) for x in row] for row in matrix]).inv()
        target_moments = power_sums(polynomial, m-q)
        for signs in product((-1, 1), repeat=q):
            solution = inverse * fmpq_mat([[s] for s in signs])
            remainder = [rational(solution[k, 0]) for k in range(q)]
            dr = derivative(remainder)
            delta = min(abs(evaluate(polynomial, t)) / (1+abs(evaluate(remainder, t)))
                        for t in endpoints) / 2
            assert delta > 0
            children = [[polynomial[k] + direction*delta*(remainder[k] if k < q else 0)
                         for k in range(m+1)] for direction in (1, -1)]
            for child in children:
                assert power_sums(child, m-q) == target_moments
                for i in range(m):
                    left, right = endpoints[2*i:2*i+2]
                    assert evaluate(child, left)*evaluate(child, right) < 0
                    for t in (left, right):
                        assert evaluate(child, t)*evaluate(polynomial, t) > 0
            for sign, t in zip(signs, queries):
                pt, dpt = evaluate(polynomial, t), evaluate(dp, t)
                rt, drt = evaluate(remainder, t), evaluate(dr, t)
                assert (drt*pt-rt*dpt)/pt**2 == sign
                plus, minus = (evaluate(child, t) for child in children)
                assert plus > 0 and minus > 0
                difference = (evaluate(derivative(children[0]), t)/plus
                              - evaluate(derivative(children[1]), t)/minus)
                assert difference == 2*delta*(drt*pt-rt*dpt)/(plus*minus)
                assert sign*difference > 0
            checked += 1
    print(f"M={m}: {checked} complete rational split certificates", flush=True)
    return checked


def product_factorials(q):
    out = 1
    for k in range(q):
        out *= factorial(k)
    return out


if __name__ == "__main__":
    total = sum(check_degree(m) for m in range(1, 9))
    assert total == sum(2**(m+1)-2 for m in range(1, 9))
    print(f"All {total} exact certificates passed; no recursive assertion tested.")
