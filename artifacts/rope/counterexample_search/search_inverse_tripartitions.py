"""Screen all tripartitions for a uniformly signed cubic inverse.

This coefficient condition is only a precursor to an all-sign-polynomial
certificate.  Neither a positive inverse nor failed LP proves a separation.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog

N = 11
PARTITIONS = []
for left in itertools.combinations(range(N), 6):
    rest = [i for i in range(N) if i not in left]
    for middle in itertools.combinations(rest, 2):
        right = [i for i in rest if i not in middle]
        PARTITIONS.append((left, middle, right))
TRIPLES = np.array([[[[i, j, k] for j in middle for k in right] for i in left]
                    for left, middle, right in PARTITIONS])
MASKS = np.arange(1 << N)
Z = 2 * ((MASKS[:, None] >> np.arange(N)) & 1) - 1
BASIS = [()] + [v for degree in range(1, 4)
                for v in itertools.combinations(range(N), degree)]
BASIS_INDEX = {v: i for i, v in enumerate(BASIS)}
FEATURES = np.array([np.prod(Z[:, term], axis=1) for term in BASIS]).T


def cubic_tensor(beta, num):
    t = np.zeros((N, N, N))
    for triple in itertools.combinations(range(N), 3):
        value = 0.
        for h in range(3):
            p, q = [v for v in range(3) if v != h]
            for i in triple:
                j, k = [v for v in triple if v != i]
                value += num[h, i + 1] * (beta[p, j] * beta[q, k] + beta[q, j] * beta[p, k])
        for order in itertools.permutations(triple):
            t[order] = value
    return t


def sign_cone(proposal, partition, matrix, inverse, sign):
    left, middle, right = partition
    beta, num = np.array(proposal['beta']), np.array(proposal['numerators'])
    scores = np.sum((num[:, 0] + Z @ num[:, 1:].T) / (1 + Z @ beta.T), axis=1)
    labels = np.sign(scores)
    if np.any(labels == 0):
        return {'status': 'zero floating score'}
    signed_inverse = sign * inverse
    epsilon = .5 * np.min(signed_inverse / signed_inverse.sum(axis=0)[None, :])
    transform = (np.eye(6) - epsilon * np.ones((6, 6))) @ signed_inverse
    transform /= abs(transform).max()
    assert transform.min() > 0
    signed = labels[:, None] * FEATURES
    functionals = []
    pairs = list(itertools.product(middle, right))
    for i in range(6):
        for col, pair in enumerate(pairs):
            if i == col:
                continue
            coefficient = np.zeros(len(BASIS))
            for row, coordinate in enumerate(left):
                coefficient[BASIS_INDEX[tuple(sorted((coordinate,) + pair))]] = -sign * transform[i, row]
            functionals.append((['off', i, col], coefficient))
    for col, pair in enumerate(pairs):
        coefficient = np.zeros(len(BASIS))
        for row, coordinate in enumerate(left):
            coefficient[BASIS_INDEX[tuple(sorted((coordinate,) + pair))]] = sign * transform[:, row].sum()
        functionals.append((['column', col], coefficient))
    successful = []
    for name, coefficient in functionals:
        result = linprog(coefficient, A_ub=-signed, b_ub=-np.ones(len(Z)),
                         bounds=[(None, None)] * len(BASIS), method='highs',
                         options={'time_limit': 5.})
        if not result.success or result.fun <= 1e-9:
            return {'status': 'no complete sign-cone certificate', 'passed': len(successful),
                    'first_failed': name, 'solver_status': int(result.status),
                    'objective': float(result.fun) if result.success else None}
        successful.append({'constraint': name, 'minimum': float(result.fun),
                           'dual': (-result.ineqlin.marginals).tolist()})
    return {'status': 'floating duals only; exact certification required',
            'passed': len(successful), 'transform': transform.tolist(), 'duals': successful}


def scan(proposal, maximum_condition=1e12):
    beta, num = np.array(proposal['beta']), np.array(proposal['numerators'])
    tensor = cubic_tensor(beta, num)
    matrices = tensor[TRIPLES[..., 0], TRIPLES[..., 1], TRIPLES[..., 2]]
    singular = np.linalg.svd(matrices, compute_uv=False)
    good = singular[:, -1] > singular[:, 0] / maximum_condition
    ids = np.flatnonzero(good)
    inverses = np.linalg.inv(matrices[good])
    positive = np.all(inverses > 0, axis=(1, 2))
    negative = np.all(inverses < 0, axis=(1, 2))
    selected = []
    for j in np.flatnonzero(positive | negative):
        index, inverse = ids[j], inverses[j]
        ratio = np.min(abs(inverse)) / np.max(abs(inverse))
        selected.append({'partition_index': int(index), 'partition': PARTITIONS[index],
                         'matrix': matrices[index].tolist(), 'inverse': inverse.tolist(),
                         'sign': 1 if positive[j] else -1, 'minimum_relative_inverse_entry': float(ratio),
                         'condition': float(singular[index, 0] / singular[index, -1])})
    selected.sort(key=lambda item: -item['minimum_relative_inverse_entry'])
    return {'nonsingular_partitions': int(good.sum()), 'signed_inverse_partitions': len(selected)}, selected


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='+', type=Path)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--dual-limit', type=int, default=0)
    args = ap.parse_args()
    for path in args.files:
        for index, line in enumerate(path.read_text().splitlines()):
            proposal = json.loads(line)
            if 'beta' not in proposal or 'numerators' not in proposal:
                continue
            start = time.time()
            diagnostic, candidates = scan(proposal)
            for candidate in candidates[:args.dual_limit]:
                candidate['sign_cone'] = sign_cone(proposal, candidate['partition'],
                    np.array(candidate['matrix']), np.array(candidate['inverse']), candidate['sign'])
            result = {'source': str(path), 'index': index, **diagnostic,
                      'seconds': time.time() - start, 'candidates': candidates[:max(args.dual_limit, 3)]}
            with args.out.open('a') as out:
                out.write(json.dumps(result) + '\n')
            print({key: value for key, value in result.items() if key != 'candidates'}, flush=True)
