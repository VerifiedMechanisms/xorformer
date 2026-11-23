#!/usr/bin/env python3
"""Exact finite tests for the grouped sparse Cauchy candidate family.

No asymptotic shattering claim is made.  Full orthant counts are certified
only when all central arrangements are simple.  Heavy enumerations should
be invoked through the repository's `heavy` wrapper.
"""
import argparse
import importlib.util
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path
from random import Random

spec = importlib.util.spec_from_file_location(
    'plane_enumerator', Path(__file__).with_name('reverse-joint-affine-plane-search.py'))
planes = importlib.util.module_from_spec(spec)
spec.loader.exec_module(planes)


def assignments(colors):
    if colors == 2:
        return [tuple(0 if j in subset else 1 for j in range(4))
                for subset in combinations(range(4), 2)]
    assert colors == 4
    return list(permutations(range(4)))


def probe(rows, colors, mode, seed):
    rng = Random(seed)
    eps = F(1, 10000)
    poles = [eps*(j+1) for j in range(4)]
    times = [1-eps*(i+1) for i in range(rows)]
    if mode == 'random':
        profiles = [[F(rng.randrange(-9, 10)) for _ in range(colors)]
                    for _ in range(rows)]
    elif mode == 'two_cloud':
        assert colors == 2
        profiles = [[F(1), F((-1)**i)+eps**2*rng.randrange(-3, 4)]
                    for i in range(rows)]
    elif mode == 'rank2':
        aa = [F(rng.randrange(-9, 10)) for _ in range(rows)]
        bb = [F(rng.randrange(-9, 10)) for _ in range(rows)]
        profiles = [[aa[i]+bb[i]*(ell+1)+eps**2*rng.randrange(-9, 10)
                     for ell in range(colors)] for i in range(rows)]
    elif mode == 'clouds':
        profiles = [[F((i % colors) == ell)+eps**2*rng.randrange(-3, 4)
                     for ell in range(colors)] for i in range(rows)]
    elif mode == 'rank1':
        profiles = [[F(1)+eps**2*rng.randrange(-9, 10)
                     for ell in range(colors)] for i in range(rows)]
    else:
        raise ValueError(mode)
    covered = set()
    exact = True
    patterns = []
    for color in assignments(colors):
        matrix = [[profiles[i][color[g]]/(times[i]-poles[g])**2
                   for g in range(4)] for i in range(rows)]
        witnesses, simple = planes.orthants(matrix, [F(0)]*rows)
        covered.update(witnesses)
        exact &= simple
        patterns.append(frozenset(witnesses))
    status = 'complete exact enumeration' if exact else 'exact witnesses only'
    print(f'G=4 D={colors} rows={rows} seed={seed} mode={mode}: '
          f'{len(covered)}/{2**rows} orthants; {status}; '
          f'{len(set(patterns))} distinct sign sets', flush=True)


def transfer_check():
    # The smallest convenient nontrivial fixed matching: three address bits,
    # one address bit choosing between the remaining two matching colors.
    d, hcount, gcount, colors, r = 3, 8, 4, 2, 3
    eps = F(1, 10000)
    poles = [eps*(g+1) for g in range(gcount)]
    p = [eps*(i+1) for i in range(r)]
    times = [1-x for x in p]
    profiles = [[F(1), F(-2)], [F(3), F(1)], [F(-1), F(4)]]
    value = [[sum(profiles[i][a]*((h >> (1+a)) & 1) for a in range(colors))
              for h in range(hcount)] for i in range(r)]
    edges = [[] for _ in range(colors)]
    for h in range(hcount):
        color = h & 1
        coordinate = 1+color
        if not ((h >> coordinate) & 1):
            edges[color].append((h, h+(1 << coordinate)))
    assert all(len(group) == gcount//colors for group in edges)
    labels = assignments(colors)
    s = len(labels)
    coefficients = [[F((g+2)*(j+1)+1) for g in range(gcount)] for j in range(s)]
    target = [[sum(coefficients[j][g]*profiles[i][labels[j][g]] /
                   (times[i]-poles[g])**2 for g in range(gcount))
               for j in range(s)] for i in range(r)]
    assert all(x for row in target for x in row)
    token = [[F(0)]*s for _ in range(hcount)]
    residue = [[F(0)]*s for _ in range(hcount)]
    edge_assignment = []
    for j, label in enumerate(labels):
        available = [list(group) for group in edges]
        assigned = []
        for g, color in enumerate(label):
            low, high = available[color].pop()
            token[low][j] = token[high][j] = poles[g]
            residue[low][j] = -coefficients[j][g]
            residue[high][j] = coefficients[j][g]
            assigned.append((low, high))
        edge_assignment.append(assigned)
    alpha = eps/100
    while True:
        row_slopes = [[p[i]+alpha*value[i][h] for i in range(r)]
                      for h in range(hcount)]
        minimum = [1-sum(row_slopes[h])-sum(token[h]) for h in range(hcount)]
        if min(x for row in row_slopes for x in row) > 0 and min(minimum) > 0:
            actual = [[sum(residue[h][j]/alpha /
                           (times[i]-token[h][j]-alpha*value[i][h])
                           for h in range(hcount)) for j in range(s)] for i in range(r)]
            if all(actual[i][j]*target[i][j] > 0 for i in range(r) for j in range(s)):
                break
        alpha /= 10
    for i in range(r):
        for j in range(s):
            for g, (low, high) in enumerate(edge_assignment[j]):
                b = times[i]-poles[g]
                exact = (coefficients[j][g]*profiles[i][labels[j][g]] /
                         ((b-alpha*value[i][high])*(b-alpha*value[i][low])))
                pair = (coefficients[j][g]/alpha)*(
                    1/(b-alpha*value[i][high])-1/(b-alpha*value[i][low]))
                assert pair == exact
    vertices = 0
    for vertex in product((0, 1), repeat=r+s):
        for h in range(hcount):
            denominator = 1-sum(row_slopes[h][i]*vertex[i] for i in range(r)) \
                -sum(token[h][j]*vertex[r+j] for j in range(s))
            assert denominator >= minimum[h] > 0
        vertices += 1
    print(f'Cube transfer: {r*s} strict signs, {r*s*gcount} exact pair identities, '
          f'{vertices} full-cube vertices, all strict slopes; alpha={alpha}.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--rows', type=int, default=7)
    parser.add_argument('--colors', type=int, choices=(2, 4), default=2)
    parser.add_argument('--mode', choices=('random', 'two_cloud', 'rank2', 'clouds', 'rank1'),
                        default='two_cloud')
    parser.add_argument('--seed', type=int, default=23)
    parser.add_argument('--transfer-only', action='store_true')
    args = parser.parse_args()
    transfer_check()
    if not args.transfer_only:
        probe(args.rows, args.colors, args.mode, args.seed)
