#!/usr/bin/env python3
"""Exact lower count from a finite eight-pole masked-Cauchy experiment.

Every sign is computed with Fraction arithmetic. NumPy only collects the
resulting integer bit patterns over all 8! permutations. This is a finite
lower count, not a completeness claim and not an asymptotic theorem.
Run as heavy python3 tree-cauchy-eight-entropy-check.py.
"""
from fractions import Fraction as F
from itertools import permutations, combinations
from functools import reduce
from random import Random
import argparse
import json
import numpy as np

parser = argparse.ArgumentParser()
parser.add_argument('--samples', type=int, default=1000)
args = parser.parse_args()
rng = Random(17)
eta, eps = F(1, 1000), F(1, 10000)
labels = [-8, -7, -4, -1, 1, 4, 7, 8]
reciprocals = [1+eps*x for x in labels]
poles = [1-1/x for x in reciprocals]
weights = [1/reduce(lambda a, b: a*b,
                   [poles[i]-poles[j] for j in range(8) if i != j], F(1))
           for i in range(8)]
# The four squared magnitudes split into pairs with equal sums.
assert 1**2+8**2 == 4**2+7**2 == 65
perms = np.array(list(permutations(range(8))), dtype=np.int16)
mask4 = np.sum(1 << perms[:, [1, 3, 5, 7]], axis=1)
mask2a = np.sum(1 << perms[:, [2, 6]], axis=1)
mask2b = np.sum(1 << perms[:, [3, 7]], axis=1)
leaf = perms[:, 4:]
subsets = {size: [(S, sum(1 << i for i in S))
                 for S in combinations(range(8), size)] for size in [2, 4]}
kernels = {size: [[1/(1+eta*u-poles[i]) for i in range(8)]
                 for u in ([-3, -1, 1, 3] if size == 4 else [-2, 2])]
           for size in [2, 4]}


def coverage(residues):
    caches = {}
    for size in [2, 4]:
        cache = np.full(256, -1, dtype=np.int32)
        for subset, mask in subsets[size]:
            values = [sum(residues[i]*kernel[i] for i in subset)
                      for kernel in kernels[size]]
            if all(values):
                cache[mask] = sum((x > 0) << i for i, x in enumerate(values))
        caches[size] = cache
    a = caches[4][mask4]
    b = caches[2][mask2a]
    c = caches[2][mask2b]
    signs = np.array([x > 0 for x in residues], dtype=np.int32)
    d = np.sum(signs[leaf]*(1 << np.arange(4)), axis=1)
    valid = (a >= 0) & (b >= 0) & (c >= 0)
    return set(map(int, np.unique(a[valid]+(b[valid] << 4)+
                                  (c[valid] << 6)+(d[valid] << 8))))


all_patterns, by_root = set(), {}
best_pool, used = 0, 0
for _ in range(args.samples):
    root_offsets = [rng.randrange(-80, 81) for _ in range(7)]
    roots = [1+eta*F(u, 10) for u in root_offsets]
    def numerator(t):
        return reduce(lambda a, b: a*b, [t-x for x in roots], F(1))
    residues = [weights[i]*numerator(poles[i]) for i in range(8)]
    assert all(residues)
    descendants = coverage(residues)
    root_values = [numerator(1+eta*u) for u in [-7, -5, -3, -1, 1, 3, 5, 7]]
    if not all(root_values):
        continue
    used += 1
    best_pool = max(best_pool, len(descendants))
    root_pattern = sum((x > 0) << i for i, x in enumerate(root_values))
    for orientation in [1, -1]:
        rp = root_pattern if orientation == 1 else 255 ^ root_pattern
        patterns = descendants if orientation == 1 else {4095 ^ x for x in descendants}
        by_root.setdefault(rp, set()).update(patterns)
        all_patterns.update((rp << 12)+x for x in patterns)
result = {
    'verification': 'exact rational lower count; no completeness or asymptotic claim',
    'seed': 17, 'samples': args.samples, 'strict_samples_used': used,
    'poles': [str(x) for x in poles], 'query_count': 20,
    'permutations_per_pool': len(perms), 'distinct_patterns': len(all_patterns),
    'sampled_root_patterns': len(by_root), 'max_single_pool_descendant_patterns': best_pool,
    'min_descendant_union_by_sampled_root': min(map(len, by_root.values())),
    'max_descendant_union_by_sampled_root': max(map(len, by_root.values())),
}
if args.samples == 1000:
    assert len(all_patterns) == 219648
    assert len(by_root) == 248
    assert best_pool == 1536
print(json.dumps(result, indent=2))
