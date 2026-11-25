#!/usr/bin/env python3
"""Check the saved 10-cube certificate using exact integer/rational arithmetic."""
import json
from fractions import Fraction
from pathlib import Path

p = Path(__file__).with_name('no-coordinate-ray-exact.json')
data = json.loads(p.read_text())
n = data['n']
rows = [[1] + [(x >> (n - 1 - i)) & 1 for i in range(n)] for x in range(2**n)]
def dot(a, b):
    return sum(x*y for x,y in zip(a,b))
Z = [rows[i] for i in data['basis']]
T = data['matrix']
a = data['numerator']
b = data['denominator']
g = data['basis_labels']
assert all(x > 0 for x in b)
assert [dot(row,b) for row in T] == a
assert [[dot(row,[T[k][j] for k in range(n+1)]) for j in range(n+1)] for row in Z] == [[s*x for x in row] for s,row in zip(g,Z)]
# Exact determinant by Gaussian elimination.
work = [[Fraction(v) for v in row] for row in Z]
det = Fraction(1)
for i in range(n+1):
    pivot = next(j for j in range(i,n+1) if work[j][i])
    if pivot != i:
        work[i],work[pivot] = work[pivot],work[i]
        det = -det
    q = work[i][i]
    det *= q
    for j in range(i+1,n+1):
        c = work[j][i]/q
        work[j] = [x-c*y for x,y in zip(work[j],work[i])]
assert det == Fraction(data['determinant']) == 1
labels = [1 if dot(row,a)>0 else -1 for row in rows]
slacks = [f*dot(row,a)-dot(row,b) for row,f in zip(rows,labels)]
assert min(slacks) == 0
assert [i for i,s in enumerate(slacks) if s==0] == data['basis'] == data['unit_contact_indices']
assert min(s for s in slacks if s) == int(data['minimum_noncontact_slack']) == 2
for j,i in enumerate(data['test_indices']):
    col = [row[j] for row in T]
    value = labels[i]*dot(rows[i],col)-rows[i][j]
    assert value == int(data['test_column_values'][j]) == -2
print(json.dumps({'arithmetic':'exact Fraction/integer', 'cube_rows':2**n,
                  'basis_determinant':str(det), 'strict_positive_denominator':True,
                  'unit_contact_count':len(data['basis']),
                  'minimum_noncontact_slack':2,
                  'coordinate_rays_excluded':n+1},indent=2))
