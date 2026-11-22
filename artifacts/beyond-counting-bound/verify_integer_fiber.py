"""Independent exact arithmetic for the integer interpolation obstruction."""

import argparse
from fractions import Fraction as Q
from itertools import combinations
import json
from pathlib import Path


def vertex(j):
    return [(j >> i) & 1 for i in range(5)]


def dot(a, b):
    return sum(x*y for x,y in zip(a,b))


def determinant(rows):
    a = [[Q(x) for x in row] for row in rows]
    n, result = len(a), Q(1)
    assert all(len(row) == n for row in a)
    for i in range(n):
        pivot = next((j for j in range(i,n) if a[j][i]), None)
        if pivot is None:
            return Q(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            result = -result
        value = a[i][i]
        result *= value
        for j in range(i+1,n):
            factor = a[j][i]/value
            for k in range(i+1,n):
                a[j][k] -= factor*a[i][k]
    return result


def evaluate(p, j):
    x = vertex(j)
    return sum(dot(u,x)/(1+dot(b,x)) for u,b in zip(p['u'],p['b']))


def jacobian(p, indices):
    out = []
    for j in indices:
        x = vertex(j)
        den = [1+dot(b,x) for b in p['b']]
        num = [dot(u,x) for u in p['u']]
        out.append([Q(x[i])/den[h] for h in range(2) for i in range(5)] +
                   [-num[h]*x[i]/den[h]**2 for h in range(2) for i in range(5)])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('certificate', type=Path)
    args = ap.parse_args()
    data = json.loads(args.certificate.read_text())
    ps = [{kind:[[Q(a) for a in row] for row in data[tag][kind]]
           for kind in ('u','b')} for tag in ('source','second')]
    for p in ps:
        assert all(len(p[t]) == 2 and all(len(row)==5 for row in p[t]) for t in ('u','b'))
        assert all(b > 0 for row in p['b'] for b in row)
    assert len(data['indices']) == len(set(data['indices'])) == 20
    assert data['indices'][:15] == list(range(1,16))
    assert all(evaluate(ps[0],j) == evaluate(ps[1],j) for j in [0]+data['indices'])
    differences = {j:evaluate(ps[0],j)-evaluate(ps[1],j) for j in range(32)}
    different = {j:str(v) for j,v in differences.items() if v}
    assert different
    js = [jacobian(p,data['indices']) for p in ps]
    dets = [determinant(j) for j in js]
    assert all(dets)
    assert dets == list(map(Q,data['determinants']))
    # Four columns for one selector coordinate, in the order u1,u2,b1,b2.
    columns = [4,9,14,19]
    common = []
    for rows in combinations(range(15,20),4):
        minors = [determinant([[j[r][c] for c in columns] for r in rows]) for j in js]
        if all(minors):
            common.append({'vertices':[data['indices'][r] for r in rows],
                           'determinants':list(map(str,minors))})
    assert common
    print(json.dumps({'status':'VERIFIED','determinants':list(map(str,dets)),
                      'held_out_differences':different,'extension_minors':common},indent=2))


if __name__ == '__main__':
    main()
