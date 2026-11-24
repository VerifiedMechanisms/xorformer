#!/usr/bin/env python3
"""Exact ranks strengthen the saved four-cone and root-bridge certificates.

No optimization solver is used. The last check proves a full-rank positive
dependence for two coalesced H32 targets, so their shared signed residue
cone remains empty for every sufficiently small positive new pole gap.
This does not assert that either target is individually infeasible.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import runpy
from flint import fmpq_mat

path = Path(__file__).parent
old = runpy.run_path(str(path / 'butterfly-biased-cone-intersection-check.py'))
data, bridge = old['data'], old['bridge']
rows_by_target, allrows = old['rows_by_target'], old['allrows']
H, C, v = old['H'], old['C'], old['v']

def rank(rows):
    return fmpq_mat([[str(a) for a in row] for row in rows]).rank()

support = [allrows[i] for i, value in data['dual']]
assert all(F(value) > 0 for i, value in data['dual'])
assert rank(support) == H

for part in bridge['partitions']:
    selected = []
    for i in part['left'] + part['right']:
        for row in rows_by_target[i]:
            selected.append(row + [sum(a*b for a, b in zip(row, v))
                                   if i in part['right'] else F(0)])
    assert all(F(value) > 0 for i, value in part['dual'])
    assert rank([selected[i] for i, value in part['dual']]) == H + 1

part = bridge['partitions'][0]
normal = list(map(F, bridge['separating_example']['normal']))
bits = bridge['separating_example']['rootword']
assert len(normal) == H and all(normal)
assert sum(normal) == 0
assert all((1-2*bit)*q < 0 for bit, q in zip(bits, normal))

# Variables are the two child-indexed residue vectors a,b and one root bias.
lifted_all = []
for i in part['left'] + part['right']:
    for row in rows_by_target[i]:
        lifted_all.append((row + [F(0)]*H if i in part['left']
                           else [F(0)]*H + row) + [F(0)])
lifted = [lifted_all[i] for i, value in part['dual']]
lam = [F(value) for i, value in part['dual']]
for s in range(H):
    sign = 1 - 2*bits[s]
    lifted.append([sign*x for x in C[s]]
                  + [-sign*x for x in C[s]] + [F(sign)])
    lam.append(abs(normal[s]))
assert len(lifted) == 2*H + 2
assert all(x > 0 for x in lam)
assert all(sum(a*row[j] for a, row in zip(lam, lifted)) == 0
           for j in range(2*H + 1))
assert rank(lifted) == 2*H + 1

# Check the two listed parent targets really have the stated child targets
# and the common forbidden root word in the established switch convention.
bf = old['bf']
parent_sw = bf.switches(data['dimension'] + 1)
child_sw = bf.switches(data['dimension'])
child_pos = {e:i for i,e in enumerate(child_sw)}
parents = bridge['separating_example']['parent_targets']
for parent, left, right in zip(parents, part['left'], part['right']):
    for i, (k,s,g) in enumerate(parent_sw):
        if k == data['dimension']:
            assert parent[i] == bits[s]
        else:
            block_count = H // (1 << (k+1))
            child = left if g < block_count else right
            assert parent[i] == data['targets'][child][child_pos[k,s,g % block_count]]

print(json.dumps(dict(weak_four_cone_dimension=0,
                      weak_quotient_bridge_dimensions=[0,0,0],
                      coalesced_parent_pair_support=len(lifted),
                      coalesced_parent_pair_rank=rank(lifted),
                      robust_shared_signed_pair_obstruction=True,
                      single_target_obstruction=False)))
