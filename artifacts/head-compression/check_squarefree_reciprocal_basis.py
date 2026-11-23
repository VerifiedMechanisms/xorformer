"""Exact finite diagnostics for the manual reciprocal-basis identities.

No finite run implies the universal head-complexity conjecture. The basis
check uses rational matrix inversion, independently of the subset proof.
"""
from fractions import Fraction as F
from itertools import combinations, product
import argparse
import json
import math
import time


def choose(a, r):
    v = F(1)
    for j in range(r):
        v *= (a - j) / F(j + 1)
    return v


def compositions(k, length):
    if length == 1:
        yield (k,)
    else:
        for j in range(k + 1):
            for tail in compositions(k - j, length - 1):
                yield (j,) + tail


def basis_checks():
    from flint import fmpq_mat
    records = []
    for n, k in [(3, 2), (4, 2), (5, 2), (6, 2), (6, 3), (8, 2)]:
        for mode in ['equal', 'distinct']:
            b = [1] * n if mode == 'equal' else list(range(1, n + 1))
            subsets = [S for j in range(k + 1) for S in combinations(range(n), j)]
            xs = [[int(i not in Z) for i in range(n)] for Z in subsets]
            def C(x):
                return 1 + sum(a * t for a, t in zip(b, x))
            def B(S, x):
                return C(x) + k - len(S) + sum(x[i] for i in S)
            matrix = fmpq_mat([[str(F(1, B(S, x))) for S in subsets] for x in xs])
            rhs = fmpq_mat([[str(F(1, C(x)))] for x in xs])
            solved = matrix.solve(rhs)
            weights = [F(str(solved[i, 0])) for i in range(len(subsets))]
            for x in product((0, 1), repeat=n):
                assert sum(w / B(S, x) for w, S in zip(weights, subsets)) == F(1, C(x))
            if mode == 'equal':
                expected = [F(2 if len(S) == k - 1 else int(len(S) == k), math.comb(n + 1, k)) for S in subsets]
                assert weights == expected
            records.append(dict(n=n, k=k, mode=mode, heads=len(subsets),
                                weights=list(map(str, weights)), exact_cube_identity=True,
                                negative_weights=sum(w < 0 for w in weights),
                                zero_weights=sum(w == 0 for w in weights)))
    return records


def binomial_checks():
    records = []
    for b in [[F(1), F(1), F(1), F(1)],
              [F(2), F(1), F(3), F(2)],
              [F(3, 2), F(2, 3), F(7, 4), F(5, 6)],
              [F(1), F(2), F(4), F(3), F(5)]]:
        n = len(b) - 1
        for step in [F(1), F(3, 2)]:
            for scale in [F(1), F(-1), F(2, 3), F(-3, 2)]:
                for k in range(5):
                    terms = []
                    for a in compositions(k, n + 1):
                        w = (1 + step * a[0] / b[0]) * math.prod(choose(v / scale, j) for v, j in zip(b, a))
                        if w:
                            terms.append((a, w))
                    normalizer = choose(sum(b) / scale, k)
                    for x in product((0, 1), repeat=n):
                        base = b[0] + sum(t * v for t, v in zip(x, b[1:]))
                        score = sum(w / (base + step * (a[0] + sum(t * j for t, j in zip(x, a[1:])))) for a, w in terms)
                        assert score == normalizer / base
                        normalized = sum(w * b[0] / (b[0] + step * a[0]) for a, w in terms)
                        assert normalized == normalizer
                    if scale < 0:
                        assert normalizer != 0
                        assert all(w / normalizer > 0 for _, w in terms)
                    records.append(dict(b=list(map(str, b)), step=str(step), scale=str(scale),
                                        k=k, nonzero_terms=len(terms), normalizer=str(normalizer),
                                        exact_cube_identity=True, normalized_weights_sum_checked=True))
    return records


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--out', required=True)
    args = p.parse_args()
    start = time.monotonic()
    result = dict(scope='Finite exact diagnostics only; universal target unproved.',
                  basis=basis_checks(), generalized_binomial=binomial_checks())
    result['seconds'] = time.monotonic() - start
    with open(args.out, 'w') as f:
        json.dump(result, f, indent=2)
        f.write('\n')
    print(json.dumps(dict(basis_cases=len(result['basis']),
                          generalized_binomial_cases=len(result['generalized_binomial']),
                          all_exact=True, seconds=result['seconds'])))


if __name__ == '__main__':
    main()
