#!/usr/bin/env python3
"""Exact finite-field probes of unbalanced reciprocal Grassmann limits.

This computes certified leading subspaces over F_p((epsilon)) to the
available series precision. It does not establish real shattering or a
universal compiler. All matrix entries and elimination steps are exact
modulo the displayed prime.
"""
import argparse
import itertools
import json
import random
import numpy as np


PRIME = 1000003


def reciprocal_series(w, v, a, b, degree, w_exp=1):
    out = np.zeros(degree + 1, dtype=np.int64)
    out[0] = 1
    for k in range(1, degree + 1):
        out[k] = ((w * int(out[k - w_exp]) if k >= w_exp else 0)
                  + (v * int(out[k - a]) if k >= a else 0)
                  + (int(out[k - b]) if k >= b else 0)) % PRIME
    return out


def inverse_series(value):
    assert value[0] != 0
    out = np.zeros(len(value), dtype=np.int64)
    out[0] = pow(int(value[0]), -1, PRIME)
    for k in range(1, len(value)):
        out[k] = (-int(out[0]) *
                  (int(np.dot(value[1:k+1], out[k-1::-1])) % PRIME)) % PRIME
    return out


def grassmann_limit(columns):
    columns = [c.copy() for c in columns]
    basis = []
    valuations = []
    while columns:
        degree = columns[0].shape[1] - 1
        choices = []
        for h, column in enumerate(columns):
            nz = np.nonzero(column)
            if len(nz[0]):
                val = int(min(nz[1]))
                row = next(i for i in range(len(column)) if column[i, val])
                choices.append((val, h, row))
        if not choices:
            raise ValueError("insufficient series precision or dependent columns")
        val, h, row = min(choices)
        pivot = columns.pop(h)[:, val:]
        degree -= val
        columns = [c[:, :degree+1] for c in columns]
        inv = inverse_series(pivot[row])
        pivot = np.array([np.convolve(c, inv)[:degree+1] % PRIME for c in pivot])
        assert pivot[row, 0] == 1 and not np.any(pivot[row, 1:])
        basis.append(pivot[:, 0].copy())
        valuations.append(val)
        for index, column in enumerate(columns):
            multiplier = column[row].copy()
            correction = np.array([
                np.convolve(c, multiplier)[:degree+1] % PRIME for c in pivot])
            columns[index] = (column - correction) % PRIME
            assert not np.any(columns[index][row])
    return np.array(basis).T, valuations


def rref_rows(rows):
    if len(rows) == 0:
        return []
    mat = [list(map(int, row)) for row in rows]
    rank = 0
    for col in range(len(mat[0])):
        found = next((i for i in range(rank, len(mat)) if mat[i][col]), None)
        if found is None:
            continue
        mat[rank], mat[found] = mat[found], mat[rank]
        inv = pow(mat[rank][col], -1, PRIME)
        mat[rank] = [x * inv % PRIME for x in mat[rank]]
        for i in range(len(mat)):
            if i != rank and mat[i][col]:
                t = mat[i][col]
                mat[i] = [(x - t*y) % PRIME for x, y in zip(mat[i], mat[rank])]
        rank += 1
        if rank == len(mat):
            break
    return mat[:rank]


def probe(heads, a, b, degree, mode, permutation_limit=0, w_exp=1, head_sign=1):
    bits = (heads - 1).bit_length()
    # Include a constant profile so no head has a zero perturbation column.
    slot_profiles = [[1] + [(h >> ell) & 1 for ell in range(bits)]
                     for h in range(heads)]
    dimension = bits + 1
    row_data = [(k+1, ell) for k in range(heads) for ell in range(dimension)]
    spaces = set()
    union = []
    val_ranges = []
    perms = list(itertools.permutations(range(heads)))
    if permutation_limit:
        random.Random(712).shuffle(perms)
        perms = perms[:permutation_limit]
    for permutation_index, perm in enumerate(perms):
        columns = []
        for h in range(heads):
            column = []
            for w, ell in row_data:
                value = reciprocal_series(w, head_sign * slot_profiles[h][ell], a[h],
                                          b[perm[h]], degree, w_exp)
                if mode == "subtracted":
                    value = (value - reciprocal_series(w, 0, a[h],
                                                       b[perm[h]], degree, w_exp)) % PRIME
                column.append(value)
            columns.append(np.array(column))
        basis, vals = grassmann_limit(columns)
        canonical = rref_rows(basis.T)
        assert len(canonical) == heads
        if permutation_index == 0:
            reversed_basis, _ = grassmann_limit(list(reversed(columns)))
            assert canonical == rref_rows(reversed_basis.T)
        spaces.add(tuple(tuple(row) for row in canonical))
        union = rref_rows(union + canonical)
        val_ranges.append(sum(vals))
    return {"heads": heads, "profile_rank": dimension, "rows": len(row_data),
            "head_exponents": a, "token_exponents": b, "w_exponent": w_exp,
            "mode": mode, "head_sign": head_sign,
            "permutations": len(perms), "flat_spaces": len(spaces),
            "union_dimension": len(union),
            "successive_valuation_sum_range": [min(val_ranges), max(val_ranges)],
            "prime": PRIME, "series_degree": degree}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--heads", type=int, default=4)
    parser.add_argument("--degree", type=int, default=120)
    parser.add_argument("--permutations", type=int, default=0)
    parser.add_argument("--trials", type=int, default=8)
    parser.add_argument("--seed", type=int, default=19)
    parser.add_argument("--w-exponent", type=int, default=1)
    parser.add_argument("--head-sign", type=int, choices=(-1, 1), default=1)
    args = parser.parse_args()
    assert args.w_exponent >= 1
    assert args.degree * (PRIME - 1)**2 < 2**63
    rng = random.Random(args.seed)
    configs = [([12]*args.heads, list(range(1, args.heads+1))),
               (list(range(2, 2+args.heads)),
                [1+2*j*j for j in range(args.heads)]),
               (list(range(2, args.heads+2)), list(range(2, args.heads+2)))]
    for _ in range(args.trials):
        configs.append(([rng.randint(2, 30) for _ in range(args.heads)],
                        sorted(rng.sample(range(1, 25), args.heads))))
    for a, b in configs:
        for mode in ("raw", "subtracted"):
            try:
                result = probe(args.heads, a, b, args.degree, mode,
                               args.permutations, args.w_exponent, args.head_sign)
            except ValueError as error:
                result = {"head_exponents": a, "token_exponents": b,
                          "mode": mode, "error": str(error)}
            print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
