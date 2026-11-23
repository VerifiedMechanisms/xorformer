#!/usr/bin/env python3
"""Finite exact union-of-Cauchy-plane coverage, with explicit rational witnesses.

This is a finite experiment, not an asymptotic compiler.  The enumeration is
complete only when each reduced hyperplane arrangement is simple; otherwise
the program labels its result as a witnessed lower bound on coverage.
"""
import argparse
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb
import random


def solve(matrix, rhs):
    n = len(matrix)
    rows = [list(row)+[rhs[i]] for i, row in enumerate(matrix)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if rows[i][j]), None)
        if pivot is None:
            return None
        rows[j], rows[pivot] = rows[pivot], rows[j]
        scale = rows[j][j]
        rows[j] = [x/scale for x in rows[j]]
        for i in range(n):
            if i != j:
                scale = rows[i][j]
                rows[i] = [x-scale*y for x, y in zip(rows[i], rows[j])]
    return [row[-1] for row in rows]


def independent_columns(matrix):
    rows = [list(row) for row in matrix]
    rank = 0
    columns = []
    for j in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        scale = rows[rank][j]
        rows[rank] = [x/scale for x in rows[rank]]
        for i in range(rank+1, len(rows)):
            scale = rows[i][j]
            rows[i] = [x-scale*y for x, y in zip(rows[i], rows[rank])]
        columns.append(j)
        rank += 1
    return columns


def orthants(matrix, bias):
    r = len(matrix)
    columns = independent_columns(matrix)
    reduced = [[row[j] for j in columns] for row in matrix]
    k = len(columns)
    witnesses = {}
    simple = True

    def record(a):
        scores = [sum(x*y for x, y in zip(row, a))+b for row, b in zip(reduced, bias)]
        if all(scores):
            pattern = sum((x > 0) << i for i, x in enumerate(scores))
            full = [F(0)]*len(matrix[0])
            for j, x in zip(columns, a):
                full[j] = x
            # Recheck every stored witness against the unreduced matrix.
            original = [sum(x*y for x, y in zip(row, full))+b
                        for row, b in zip(matrix, bias)]
            assert all(original)
            assert pattern == sum((x > 0) << i for i, x in enumerate(original))
            witnesses[pattern] = full

    record([F(0)]*k)
    if k == 0:
        return witnesses, all(bias)
    if not any(bias):
        # Every chamber of an essential central arrangement has an extreme
        # ray.  Enumerate its k-1 independent active walls, with both rays.
        for active in combinations(range(r), k-1):
            for axis in range(k):
                unit = [F(j == axis) for j in range(k)]
                square = [reduced[i] for i in active]+[unit]
                ray = solve(square, [F(0)]*(k-1)+[F(1)])
                if ray is not None:
                    break
            else:
                continue
            for orientation in (-1, 1):
                vertex = [orientation*x for x in ray]
                scores = [sum(x*y for x,y in zip(row,vertex)) for row in reduced]
                if any(scores[i] == 0 for i in range(r) if i not in active):
                    simple = False
                for signs in product((-1, 1), repeat=k-1):
                    direction = solve(square, list(map(F,signs))+[F(0)])
                    assert direction is not None
                    derivatives = [sum(x*y for x,y in zip(row,direction)) for row in reduced]
                    step = min([F(1)]+[abs(scores[i])/(2*abs(derivatives[i]))
                                       for i in range(r) if scores[i] and derivatives[i]])
                    record([x+step*y for x,y in zip(vertex,direction)])
        return witnesses, simple
    for active in combinations(range(r), k):
        square = [reduced[i] for i in active]
        vertex = solve(square, [-bias[i] for i in active])
        if vertex is None:
            continue
        scores = [sum(x*y for x, y in zip(row, vertex))+b
                  for row, b in zip(reduced, bias)]
        if any(scores[i] == 0 for i in range(r) if i not in active):
            simple = False
        for signs in product((-1, 1), repeat=k):
            direction = solve(square, list(map(F, signs)))
            assert direction is not None
            derivatives = [sum(x*y for x, y in zip(row, direction)) for row in reduced]
            step = min([F(1)]+[abs(scores[i])/(2*abs(derivatives[i]))
                               for i in range(r) if scores[i] and derivatives[i]])
            record([x+step*y for x, y in zip(vertex, direction)])
    return witnesses, simple


def self_test():
    for k in range(1, 4):
        r = k+4
        matrix = [[F(i+1)**j for j in range(k)] for i in range(r)]
        central, exact = orthants(matrix, [F(0)]*r)
        assert exact and len(central) == 2*sum(comb(r-1,j) for j in range(k))
        affine, exact = orthants(matrix, [F(i+1)**k for i in range(r)])
        assert exact and len(affine) == sum(comb(r,j) for j in range(k+1))
    print("Exact enumeration self-tests: six moment-curve arrangements passed.", flush=True)


def run(n, r, seed, mode):
    rng = random.Random(seed)
    eps = F(1, 100000)
    lam = [eps*(j+1) for j in range(n)]
    offsets = [[F(rng.randrange(1, 12)) for _ in range(n)] for _ in range(r)]
    poles = [[1-eps*x for x in row] for row in offsets]
    identity = [[1/(poles[i][h]-lam[h]) for h in range(n)] for i in range(r)]
    q = [list(row) for row in identity]
    if mode in ("perturbed", "central_perturbed"):
        q = [[x+eps**2*rng.randrange(-4, 5) for x in row] for row in q]
    if mode in ("zero_bias", "central_perturbed"):
        bias = [F(0)]*r
    elif mode == "structured_bias":
        coefficients = [F(2*h+1-n) for h in range(n)]
        bias = [sum(x*y for x, y in zip(row, coefficients)) for row in offsets]
    else:
        bias = [F(rng.randrange(1, 100)) for _ in range(r)]
    covered = set()
    simple = True
    per_plane = []
    for p in permutations(range(n)):
        inverse = [p.index(j) for j in range(n)]
        matrix = [[1/(poles[i][inverse[j]]-lam[j])-q[i][j]
                   for j in range(n)] for i in range(r)]
        found, exact = orthants(matrix, bias)
        covered.update(found)
        simple &= exact
        per_plane.append(len(found))
    status = "complete exact enumeration" if simple else "exact witnesses only (degenerate arrangement)"
    print(f"H={n} rows={r} seed={seed} mode={mode}: {len(covered)}/{2**r} orthants; {status}; per-plane={per_plane}", flush=True)
    return len(covered) == 2**r


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--heads", type=int, default=3)
    parser.add_argument("--rows", type=int, default=7)
    parser.add_argument("--seed", type=int, default=20261123)
    parser.add_argument("--mode", choices=("identity", "perturbed", "structured_bias", "zero_bias", "central_perturbed"), default="identity")
    args = parser.parse_args()
    self_test()
    run(args.heads, args.rows, args.seed, args.mode)
