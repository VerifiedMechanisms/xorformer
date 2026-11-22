"""Exact finite audit of the positive exponential table construction."""
from fractions import Fraction as Q
from math import comb, factorial
import json
from pathlib import Path


def coefficients(n):
    q = Q(1, 4*n*(n+1)*2**n)
    c = [sum(Q(comb(n-k, j)*factorial(j)*factorial(k), factorial(j+k+1)) *
             (-q)**(n-k-j) for j in range(n-k+1)) / (1-q)**n
         for k in range(n+1)]
    bound = Q(3, 4*(n+1)*2**n) / (1-q)**n
    assert all(v >= bound for v in c)
    for size in range(n+1):
        value = sum(comb(size, overlap)*comb(n-size, k-overlap)*c[k]*q**overlap
                    for k in range(n+1)
                    for overlap in range(max(0, k-(n-size)), min(k, size)+1))
        assert value == Q(1, 1+size)
    return q, c


def inverse_table(values, q, n):
    out = list(map(Q, values))
    for bit in range(n):
        for s in range(2**n):
            if not (s >> bit) & 1:
                t = s | (1 << bit)
                a, b = out[s], out[t]
                out[s], out[t] = (b-q*a)/(1-q), (a-b)/(1-q)
    return out


def main():
    count = 0
    dimensions = []
    for n in range(1, 11):
        q, c = coefficients(n)
        dimensions.append({'n': n, 'q': str(q), 'minimum_coefficient': str(min(c))})
        if n > 3:
            continue
        m = 2**n
        epsilon = Q(1, 4*(n+1)*4**n)
        baseline = [c[t.bit_count()] for t in range(m)]
        for pattern in range(2**m):
            labels = [1 if (pattern >> s) & 1 else -1 for s in range(m)]
            d = inverse_table(labels, q, n)
            for sign in (-1, 1):
                perturbed = [a+sign*epsilon*b for a, b in zip(baseline, d)]
                assert all(a > 0 for a in perturbed)
                for s in range(m):
                    value = sum(perturbed[t] * q**((s & t).bit_count()) for t in range(m))
                    assert value == Q(1, 1+s.bit_count()) + sign*epsilon*labels[s]
                    count += 1
    report = {'status': 'PASS', 'symmetric_baseline_dimensions': dimensions,
              'all_labelings_checked_dimensions': [1, 2, 3],
              'perturbed_vertex_values_checked': count,
              'general_theorem': 'written tensor-inverse and coefficient estimates',
              'main_target_proved': False}
    Path(__file__).with_name('complete-monotonicity-checks.json').write_text(json.dumps(report, indent=2)+'\n')
    print({'status': 'PASS', 'perturbed_vertex_values_checked': count})


if __name__ == '__main__':
    main()
