#!/usr/bin/env python3
"""Finite germ-shattering search; computational evidence, not asymptotics.

The cost of sigma is sum_i (1-e*(i+sigma(i)))**-1. For sufficiently
small positive e, differences are ordered lexicographically by integer
power sums. A threshold between two costs is their average, so strict
signs are automatic. The Boolean matrix uses all right translates.
"""
import argparse
import itertools
import json
import math
import time
from fractions import Fraction

import numpy as np


def prepare(n, antisymmetric=False):
    p = np.array(list(itertools.permutations(range(n))), dtype=np.int16)
    m = len(p)
    # At most 2*n-1 distinct sums; their first 2*n-1 moments determine
    # the histogram, by the Vandermonde determinant.
    signatures = [tuple(sum(((i - int(s[i])) if antisymmetric else 1)
                           * (i + 2 + int(s[i])) ** k for i in range(n))
                        for k in range(2, 2*n)) for s in p]
    vals = sorted(set(signatures))
    vrank = {v: i for i, v in enumerate(vals)}
    ranks = np.array([vrank[v] for v in signatures], dtype=np.int32)
    weights = n ** np.arange(n, dtype=np.int64)
    lookup = np.full(n**n, -1, dtype=np.int32)
    lookup[p.astype(np.int64) @ weights] = np.arange(m)
    costs = np.empty((m, m), dtype=np.int32)
    for j, tau in enumerate(p):
        inv = np.argsort(tau)
        composition = p[:, inv]
        costs[j] = ranks[lookup[composition.astype(np.int64) @ weights]]
    return p, vals, ranks, costs


def search(matrix, target, attempts, rng):
    """Randomized greedy with exact split/coverage tests at each step."""
    m = matrix.shape[0]
    best = []
    best_min = 0
    for attempt in range(attempts):
        chosen = [0]
        labels = matrix[0].astype(np.int16)
        while len(chosen) < target:
            cells = [np.flatnonzero(labels == k) for k in range(1 << len(chosen))]
            if any(len(c) < 2 for c in cells):
                break
            # A row is eligible iff it splits every existing cell.
            eligible = np.ones(m, dtype=bool)
            balance = np.full(m, m, dtype=np.int32)
            entropy = np.zeros(m, dtype=np.float64)
            for cell in sorted(cells, key=len):
                ids = np.flatnonzero(eligible)
                if not len(ids):
                    break
                cnt = np.count_nonzero(matrix[np.ix_(ids, cell)], axis=1)
                mn = np.minimum(cnt, len(cell) - cnt)
                eligible[ids[mn == 0]] = False
                balance[ids] = np.minimum(balance[ids], mn)
                entropy[ids] += np.log(np.maximum(mn, 1))
            ids = np.flatnonzero(eligible)
            if not len(ids):
                break
            # Mix greedy balance and randomized choices to avoid one orbit.
            if attempt % 3 == 0:
                score = balance[ids].astype(float) + rng.random(len(ids)) * 2.5
            elif attempt % 3 == 1:
                score = entropy[ids] + rng.random(len(ids)) * 3.0
            else:
                score = rng.random(len(ids))
            pick = int(ids[np.argmax(score)])
            labels += matrix[pick].astype(np.int16) << len(chosen)
            chosen.append(pick)
        counts = np.bincount(labels, minlength=1 << len(chosen))
        minimum = int(counts.min())
        if len(chosen) > len(best) or (len(chosen) == len(best) and minimum > best_min):
            best, best_min = chosen, minimum
        if len(chosen) >= target:
            witnesses = [int(np.flatnonzero(labels == k)[0]) for k in range(1 << target)]
            return best, best_min, witnesses
    return best, best_min, None


def exhaustive_search(matrix, target):
    """Exhaust every query subset, fixing the identity by translation."""
    m = len(matrix)
    full = (1 << m) - 1
    bits = [sum(1 << int(i) for i in np.flatnonzero(row)) for row in matrix]
    nodes = [0] * (target + 1)

    def descend(chosen, cells, candidates):
        nodes[len(chosen)] += 1
        if len(chosen) == target:
            return chosen
        need = target - len(chosen)
        if any(c.bit_count() < (1 << need) for c in cells):
            return None
        eligible = []
        for q in candidates:
            if all((c & bits[q]) and (c & (full ^ bits[q])) for c in cells):
                eligible.append(q)
        if len(eligible) < need:
            return None
        for pos, q in enumerate(eligible):
            if len(eligible) - pos < need:
                break
            newcells = [part for c in cells for part in (c & bits[q], c & (full ^ bits[q]))]
            ans = descend(chosen + [q], newcells, eligible[pos+1:])
            if ans is not None:
                return ans
        return None

    return descend([0], [bits[0], full ^ bits[0]], list(range(1, m))), nodes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, required=True)
    ap.add_argument('--attempts', type=int, default=30)
    ap.add_argument('--target', type=int)
    ap.add_argument('--seed', type=int, default=725)
    ap.add_argument('--output')
    ap.add_argument('--exhaustive', action='store_true')
    ap.add_argument('--antisymmetric', action='store_true')
    ap.add_argument('--verify-certificate')
    args = ap.parse_args()
    if args.verify_certificate:
        data = json.load(open(args.verify_certificate))
        cert = data['certificate']
        n = data['n']
        assert data['antisymmetric']
        eps = Fraction(1, 10**6)
        def sig(a, b):
            return tuple(sum((x-y)*(x+y)**k for x, y in zip(a, b))
                         for k in range(2, 2*n))
        def value(a, b):
            return sum(Fraction(x-y)/(1-eps*(x+y)) for x, y in zip(a, b))
        identity = tuple(range(1, n+1))
        endpoints = []
        for signature in [cert['lower_signature'], cert['upper_signature']]:
            witness = next(p for p in itertools.permutations(identity)
                           if sig(identity, p) == tuple(signature))
            endpoints.append(value(identity, witness))
        threshold = sum(endpoints)/2
        assert len(cert['witness_permutations']) == 1 << len(cert['query_permutations'])
        margin = None
        for word, perm in enumerate(cert['witness_permutations']):
            b = [x+1 for x in perm]
            assert sorted(b) == list(identity)
            for bit, tau in enumerate(cert['query_permutations']):
                a = [x+1 for x in tau]
                assert sorted(a) == list(identity)
                score = value(a, b) - threshold
                assert score != 0 and (score > 0) == bool(word >> bit & 1)
                margin = abs(score) if margin is None else min(margin, abs(score))
        bound = 1-eps*n*(len(cert['query_permutations'])+len(cert['witness_permutations']))
        assert bound > 0
        print('Exact rational certificate verified; minimum margin:', margin)
        print('Full cube denominator lower bound:', bound)
        return
    start = time.time()
    p, vals, ranks, costs = prepare(args.n, args.antisymmetric)
    target = args.target or args.n + 1
    rng = np.random.default_rng(args.seed)
    # Balanced germ cuts, including nearby ties where higher moments matter.
    median = int(np.median(ranks))
    cuts = list(dict.fromkeys([median + d for d in [0, -1, 1, -2, 2, -4, 4, -8, 8]]))
    cuts += [int(np.quantile(ranks, q)) for q in [.35, .4, .45, .55, .6, .65]]
    if args.exhaustive:
        cuts = range(len(vals)-1)
    best = []
    result = {'n': args.n, 'antisymmetric': args.antisymmetric,
              'states': len(p), 'cost_levels': len(vals), 'trials': []}
    for cut in dict.fromkeys(cuts):
        if cut < 0 or cut >= len(vals)-1:
            continue
        mat = costs > cut
        if args.exhaustive:
            rows, nodes = exhaustive_search(mat, target)
            trial = {'cut': cut, 'rows': rows, 'nodes': nodes}
            print(json.dumps(trial), flush=True)
            result['trials'].append(trial)
            if rows is not None:
                best = rows
                break
            continue
        rows, minimum, witnesses = search(mat, target, args.attempts, rng)
        trial = {'cut': cut, 'density': float(mat[0].mean()), 'rows': rows,
                 'minimum_cell': minimum, 'queries': p[rows].tolist()}
        print(json.dumps(trial), flush=True)
        result['trials'].append(trial)
        if len(rows) > len(best):
            best = rows
        if witnesses is not None:
            result['certificate'] = {'cut': cut, 'query_permutations': p[rows].tolist(),
                                     'witness_permutations': p[witnesses].tolist(),
                                     'lower_signature': vals[cut], 'upper_signature': vals[cut+1]}
            break
    result['best'] = len(best)
    result['seconds'] = time.time() - start
    print(json.dumps({'n': args.n, 'best': len(best), 'seconds': result['seconds']}), flush=True)
    if args.output:
        with open(args.output, 'w') as f:
            json.dump(result, f, indent=2)


if __name__ == '__main__':
    main()
