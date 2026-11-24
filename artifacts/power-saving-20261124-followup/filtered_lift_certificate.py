"""Exact rational instance of the positive simplex-grid filtered lift.

This is a finite computation, not a proof of the general theorem.
"""
import itertools
import json
from pathlib import Path
import sympy as sp

DIRECTION_DIMENSION = 2
ORDER = 3
BASELINE = (1, 1)
POINTS = [(1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 1), (3, 3)]
WEIGHTS = [1, -4, 3, 4, -4, -1, 1]
GRID = [b for b in itertools.product(range(ORDER + 1), repeat=DIRECTION_DIMENSION)
        if sum(b) <= ORDER]
T = sp.symbols('t0:2')

def binomial_poly(u, k):
    return sp.prod(u - j for j in range(k)) / sp.factorial(k)

def lagrange(beta):
    return sp.expand(sp.prod(binomial_poly(T[i], beta[i])
                            for i in range(DIRECTION_DIMENSION)) *
                     binomial_poly(ORDER - sum(T), ORDER - sum(beta)))

basis = [lagrange(b) for b in GRID]
interpolation_matrix = sp.Matrix([[p.subs(dict(zip(T, gamma))) for p in basis]
                                  for gamma in GRID])
assert interpolation_matrix == sp.eye(len(GRID))
aux_weights = [sp.simplify(sum(c * p.subs(dict(zip(T, [w[i] - BASELINE[i]
                        for i in range(DIRECTION_DIMENSION)])))
                        for c, w in zip(WEIGHTS, POINTS))) for p in basis]
aux_points = [tuple(BASELINE[i] + b[i] for i in range(DIRECTION_DIMENSION))
              for b in GRID]
ordinary_moments = []
for alpha in GRID:
    before = sum(c * sp.prod(w[i] ** alpha[i] for i in range(DIRECTION_DIMENSION))
                 for c, w in zip(WEIGHTS, POINTS))
    auxiliary = sum(c * sp.prod(w[i] ** alpha[i] for i in range(DIRECTION_DIMENSION))
                    for c, w in zip(aux_weights, aux_points))
    assert before == auxiliary
    ordinary_moments.append({'multi_index': alpha, 'original': str(before),
                             'auxiliary': str(auxiliary), 'difference': '0'})
projection_group_sums = []
for x in itertools.product([0, 1], repeat=DIRECTION_DIMENSION):
    groups = {}
    for c, w in zip(aux_weights, aux_points):
        projection = sum(w[i] * x[i] for i in range(DIRECTION_DIMENSION))
        groups[projection] = groups.get(projection, sp.Integer(0)) + c
    assert all(value == 0 for value in groups.values())
    projection_group_sums.append({'query': x,
        'group_sums': {str(k): str(value) for k, value in sorted(groups.items())}})
result = {'status': 'exact rational finite computation',
          'dimension': DIRECTION_DIMENSION, 'order': ORDER,
          'grid_size': len(GRID), 'grid_bound': int(sp.binomial(DIRECTION_DIMENSION + ORDER, ORDER)),
          'interpolation_matrix_is_identity': True,
          'nonzero_auxiliary_atoms': [{'point': w, 'weight': str(c)}
                                    for c, w in zip(aux_weights, aux_points) if c != 0],
          'ordinary_moments': ordinary_moments,
          'projection_group_sums': projection_group_sums}
output = Path(__file__).with_suffix('.json')
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'output': str(output), 'grid_size': len(GRID),
                  'nonzero_auxiliary_atoms': len(result['nonzero_auxiliary_atoms']),
                  'all_exact_checks_pass': True}, indent=2))
