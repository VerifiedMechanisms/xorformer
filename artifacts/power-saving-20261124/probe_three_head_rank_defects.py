"""Finite-field discovery only; any candidate requires exact rational verification."""
from itertools import combinations, product
import json
import numpy as np

MOD = 65521
N = 6
XS = np.array(list(product((0, 1), repeat=N)), dtype=np.int64)
SLOPES = np.array(list(product((1, 2), repeat=N)), dtype=np.int64)

def rank_mod(matrix):
    a = matrix.copy() % MOD
    row = 0
    for col in range(a.shape[1]):
        nz = np.flatnonzero(a[row:, col])
        if not len(nz):
            continue
        pivot = row + int(nz[0])
        a[[row, pivot]] = a[[pivot, row]]
        a[row] = a[row] * pow(int(a[row, col]), -1, MOD) % MOD
        if row + 1 < a.shape[0]:
            a[row + 1:] = (a[row + 1:] - a[row + 1:, col, None] * a[row]) % MOD
        row += 1
        if row == a.shape[1]:
            return row
    return row

atoms = []
for b in SLOPES:
    values = 1 + XS @ b
    inverses = np.array([pow(int(v), -1, MOD) for v in values], dtype=np.int64)
    atoms.append(XS * inverses[:, None] % MOD)
one = np.ones((len(XS), 1), dtype=np.int64)
bad_pairs = set()
for i, j in combinations(range(len(atoms)), 2):
    if rank_mod(np.concatenate((one, atoms[i], atoms[j]), axis=1)) < 1 + 2*N:
        bad_pairs.add((i, j))
print(json.dumps({"phase": "pairs", "bad_pairs": len(bad_pairs)}), flush=True)

tested = 0
candidates = []
for ids in combinations(range(len(atoms)), 3):
    if any(pair in bad_pairs for pair in combinations(ids, 2)):
        continue
    bmat = np.concatenate((np.ones((3, 1), dtype=np.int64), SLOPES[list(ids)]), axis=1)
    if rank_mod(bmat.T) < 3:
        continue
    tested += 1
    rank = rank_mod(np.concatenate((one, *(atoms[i] for i in ids)), axis=1))
    if rank < 1 + 3*N:
        candidate = {"ids": ids, "slopes": SLOPES[list(ids)].tolist(), "rank_mod": rank}
        candidates.append(candidate)
        print(json.dumps({"phase": "candidate", **candidate}), flush=True)
        if len(candidates) == 10:
            break
print(json.dumps({"phase": "done", "tested": tested, "candidates": candidates}), flush=True)
