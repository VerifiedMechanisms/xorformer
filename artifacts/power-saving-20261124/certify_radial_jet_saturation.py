#!/usr/bin/env python3
"""Finite exact modular minor certificate used with the written rank bounds."""
import json
from pathlib import Path
import numpy as np
from probe_radial_jet_spans import PRIME, moments, rref

mats, directions = moments(6, 8, 3, 1, 'generic')
N, d = mats[0].shape
blocks = [np.concatenate([mats[k-j] if k >= j else np.zeros((N,d), dtype=np.int64)
                          for j in range(3)], axis=1) for k in range(4)]
stack = np.concatenate(blocks, axis=0)
_, rows = rref(stack.T)
_, cols = rref(stack[rows,:])
minor = stack[np.ix_(rows,cols)].copy() % PRIME
assert minor.shape == (119,119)
det = 1
for j in range(len(rows)):
    choices = np.flatnonzero(minor[j:,j])
    assert len(choices)
    k = j + int(choices[0])
    if k != j:
        minor[[j,k]] = minor[[k,j]]
        det = -det
    pivot = int(minor[j,j])
    det = det * pivot % PRIME
    minor[j] = minor[j] * pow(pivot,-1,PRIME) % PRIME
    factors = minor[j+1:,j].copy()
    minor[j+1:] = (minor[j+1:] - factors[:,None] * minor[j][None,:]) % PRIME
assert det != 0
result = dict(kind='exact_finite_minor_certificate_with_separate_written_structural_bounds',
              prime=PRIME,n=6,heads=8,numerator_jet_degree=2,leading_order=3,
              directions=directions,stack_shape=list(stack.shape),
              row_indices=rows,column_indices=cols,minor_size=len(rows),
              determinant_mod_prime=int(det),lower_stack_rank_upper_bound=7+22+42,
              leading_image_rank_lower_bound=len(rows)-(7+22+42),
              formal_column_count=d)
print(json.dumps(result,indent=2))
