"""Balanced pure-three Cauchy extensions near the positivity boundary.

Every label and pure parameter is exact.  Numerical vanilla fitting is only a
screen: a missing fit is never a lower bound.  Run campaigns with ``heavy``.
The first three coordinates with all remaining bits zero restrict to parity.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import sys
import time

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'higher_search'))
from search_small_exact import solve_all_orientations
from search_vandermonde_perturb import fit_vanilla, vertices


def balanced_extra(count, total, maximum_l1, extremity, rng):
    """Integer vector of prescribed sum, close to a prescribed l1 radius."""
    direction = rng.normal(size=count)
    direction -= direction.mean()
    base = np.full(count, total / count)

    def rounded(scale):
        values = np.rint(base + scale * direction).astype(int)
        # Moving a single random coordinate preserves the generic directions.
        values[correction] += total - int(values.sum())
        return values

    correction = int(rng.integers(count))
    target = abs(total) + extremity * (maximum_l1 - abs(total))
    lo, hi = 0.0, float(maximum_l1 + abs(total) + 1)
    best = rounded(0)
    for _ in range(60):
        mid = (lo + hi) / 2
        trial = rounded(mid)
        if np.abs(trial).sum() <= target:
            best = trial
            lo = mid
        else:
            hi = mid
    assert best.sum() == total and np.abs(best).sum() <= maximum_l1
    return best.tolist()


def candidate(n, rng, extremity, pole_units, token_scale=0):
    ts = [Q(v, 1000) for v in pole_units]
    constant = 1 / (ts[0] * ts[1] * ts[2])
    atoms = []
    for h, t in enumerate(ts):
        pole = -1 / t
        eta = pole ** 3 - 4 * pole
        for j, other in enumerate(ts):
            if j != h:
                eta /= 1 + other * pole
        first = pole_units[h]
        center = 1000 - 3 * first
        extra = balanced_extra(n - 3, -3 * first,
                               center - n - 3 * first - 1,
                               extremity, rng)
        beta = [first] * 3 + extra
        gamma = center - sum(abs(v) for v in beta) - n
        assert sum(beta) == 0 and gamma > 0
        masses = [abs(v) + 1 for v in beta]
        token_value = int(rng.integers(-token_scale, token_scale + 1)) if token_scale else 0
        # On the parity face, D=1000+first*(z0+z1+z2).  Its
        # affine numerator is the original constant plus ratio*D, so a
        # compensating readout shift leaves the parity score unchanged.
        ratio = Q(token_value * masses[0], first)
        query_numerator = 1000 * eta + 1000 * ratio + token_value * sum(masses[3:])
        constant -= ratio
        atoms.append({'a': [mass - v for mass, v in zip(masses, beta)],
                      'b': [mass + v for mass, v in zip(masses, beta)],
                      'gamma': gamma,
                      'eta': [query_numerator.numerator, query_numerator.denominator],
                      'v0': -token_value, 'v1': token_value})
    scores = [constant + sum((Q(*p['eta']) +
               sum(p['b'][i] * p['v1'] if mask >> i & 1
                   else p['a'][i] * p['v0'] for i in range(n))) /
               (p['gamma'] + sum(p['b'][i] if mask >> i & 1 else p['a'][i]
                                  for i in range(n))) for p in atoms)
              for mask in range(1 << n)]
    if any(score == 0 for score in scores):
        epsilon = min(abs(score) for score in scores if score) / 2
        constant += epsilon
        scores = [score + epsilon for score in scores]
    labels = np.array([1 if score > 0 else -1 for score in scores])
    assert all(labels[mask] == np.prod([2 * ((mask >> i) & 1) - 1
                                      for i in range(3)]) for mask in range(8))
    margin = min(abs(score) for score in scores)
    truth = sum(int(sign > 0) << mask for mask, sign in enumerate(labels))
    return labels, {'n': n, 'atoms': atoms,
                    'constant': [constant.numerator, constant.denominator],
                    'truth_table': hex(truth),
                    'minimum_margin': [margin.numerator, margin.denominator],
                    'parity_three_restriction':
                    'coordinates0,1,2 free; all other bits zero',
                    'slope_balance': 'each head has sum_i(b_i-a_i)=0',
                    'extremity': extremity, 'pole_units': pole_units,
                    'token_scale': token_scale}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--n', type=int, default=10)
    parser.add_argument('--samples', type=int, default=12)
    parser.add_argument('--restarts', type=int, default=4)
    parser.add_argument('--seed', type=int, default=923744)
    parser.add_argument('--extremity', type=float, default=.98)
    parser.add_argument('--pole-units', type=int, nargs=3, default=[20, 50, 80])
    parser.add_argument('--token-scale', type=int, default=0)
    parser.add_argument('--nra-timeout', type=int, default=0)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    z = vertices(args.n)
    for sample in range(args.samples):
        start = time.time()
        labels, record = candidate(args.n, rng, args.extremity, args.pole_units,
                                   args.token_scale)
        fit = fit_vanilla(z, labels, args.restarts, rng)
        record.update(sample=sample, seed=args.seed, vanilla_search=fit,
                      seconds=time.time() - start)
        if fit['status'] == 'unresolved' and args.nra_timeout:
            record['NRA'] = solve_all_orientations(record, args.nra_timeout)
        with args.out.open('a') as output:
            output.write(json.dumps(record) + '\n')
        print(sample, fit['status'], fit['loss'],
              round(record['seconds'], 2), flush=True)


if __name__ == '__main__':
    main()
