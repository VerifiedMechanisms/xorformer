"""Exact finite-grid audit of D_i + (p/q)L for the replicated H=3 source.

Every six-count pattern is checked by integer arithmetic. A failure only
refutes this particular denominator shift; it is never a lower-bound claim.
Run substantial searches through the repository's `heavy` wrapper.
"""

import argparse
import itertools
import json
from pathlib import Path
import time

import numpy as np


def check(m, p, q, chunk=32):
    assert 0 < m <= 100 and 1 <= q
    max_linear, max_numerator, max_z = 63*m, 42*m, 6*m
    max_source = 3*max_numerator*(206*m)**2
    max_cross = 800*m*max_linear + 2*max_linear*18*m + 3*max_numerator*max_z
    max_shifted = q*q*max_source + abs(q*p)*max_linear*max_cross + 2*p*p*max_linear**3
    assert max_shifted < 2**63, 'integer-array overflow bound exceeded'
    rows = np.array(list(itertools.product(range(-3*m, 3*m+1, 2), repeat=3)), dtype=np.int64)
    b = rows[None, :, :]
    bs = b.sum(axis=2)
    failures = zero_boundary = linear_disagreements = 0
    first = None
    for start in range(0, len(rows), chunk):
        a = rows[start:start+chunk, None, :]
        asum = a.sum(axis=2)
        total = asum + bs
        linear = 4*asum + 3*bs
        z = a-b
        numerator = 2*(total[:, :, None]+a)
        denominator = 200*m+z
        source = sum(numerator[:, :, i]*denominator[:, :, (i+1)%3]*denominator[:, :, (i+2)%3]
                     for i in range(3))
        cross = 800*m*linear + 2*linear*z.sum(axis=2) - (numerator*z).sum(axis=2)
        shifted = q*q*source + q*p*linear*cross + 2*p*p*linear*linear*linear
        bad = (source > 0) != (shifted > 0)
        linear_disagreements += int(np.count_nonzero((source > 0) != (linear > 0)))
        count = int(np.count_nonzero(bad))
        failures += count
        zero_boundary += int(np.count_nonzero((shifted == 0) & (linear != 0)))
        if count and first is None:
            i, j = np.argwhere(bad)[0]
            first = {'A_numerators': rows[start+i].tolist(), 'B_numerators': rows[j].tolist(),
                     'L_numerator': int(linear[i,j]), 'source_cleared': int(source[i,j]),
                     'shifted_cleared': int(shifted[i,j])}
    return {'replicas': m, 'p': p, 'q': q, 'patterns': len(rows)**2,
            'strict_orientation': 3*p > q or 4*p < -q, 'disagreements': failures,
            'linear_disagreements': linear_disagreements,
            'off_hyperplane_shifted_zeros': zero_boundary, 'first_disagreement': first}


def verify_affine_record(path):
    """Independent direct row evaluation, without the shift expansion."""
    record = json.loads(Path(path).read_text())
    ds, ns = record['denominators'], record['numerators']
    assert len(ds) == len(ns) == 3
    for row in ds+ns:
        assert len(row) == 7 and all(type(v) is int for v in row)
    for row in ds:
        assert row[0] > sum(abs(v) for v in row[1:])
        assert all(v > 0 for v in row[1:]) or all(v < 0 for v in row[1:])
    total_patterns = 0
    for m in record['replicas']:
        assert type(m) is int and m > 0
        bound_n = max(sum(abs(v)*3*m for v in row) for row in ns)
        bound_d = max(sum(abs(v)*3*m for v in row) for row in ds)
        assert 3*bound_n*bound_d**2 < 2**63
        assert 3*(42*m)*(206*m)**2 < 2**63
        rows = np.array(list(itertools.product(range(-3*m, 3*m+1, 2), repeat=3)), dtype=np.int64)
        b = rows[None, :, :]
        for start in range(0, len(rows), 32):
            a = rows[start:start+32, None, :]
            total = a.sum(axis=2)+b.sum(axis=2)
            source_n = [2*(total+a[:, :, i]) for i in range(3)]
            source_d = [200*m+a[:, :, i]-b[:, :, i] for i in range(3)]
            source = sum(source_n[i]*source_d[(i+1)%3]*source_d[(i+2)%3] for i in range(3))
            den = [row[0]*3*m+sum(row[j+1]*a[:, :, j]+row[j+4]*b[:, :, j]
                   for j in range(3)) for row in ds]
            num = [row[0]*3*m+sum(row[j+1]*a[:, :, j]+row[j+4]*b[:, :, j]
                   for j in range(3)) for row in ns]
            assert all(np.all(d > 0) for d in den)
            candidate = sum(num[i]*den[(i+1)%3]*den[(i+2)%3] for i in range(3))
            assert np.all((source > 0) == (candidate > 0))
        total_patterns += len(rows)**2
        print(m, len(rows)**2, 'direct affine row patterns verified', flush=True)
    print(total_patterns, 'total patterns verified independently', flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--min-replicas', type=int, default=1)
    parser.add_argument('--max-replicas', type=int, default=8)
    parser.add_argument('--p', type=int, default=34)
    parser.add_argument('--q', type=int, default=100)
    parser.add_argument('--stop-first-failure', action='store_true')
    parser.add_argument('--write-certificate')
    parser.add_argument('--verify-affine')
    args = parser.parse_args()
    if args.verify_affine:
        verify_affine_record(args.verify_affine)
        return
    results = []
    for m in range(args.min_replicas, args.max_replicas+1):
        start = time.monotonic()
        result = check(m, args.p, args.q)
        result['seconds'] = time.monotonic()-start
        results.append(result)
        print(json.dumps(result), flush=True)
        if result['disagreements'] and args.stop_first_failure:
            break
    if args.write_certificate:
        assert results and all(r['strict_orientation'] and r['disagreements'] == 0 for r in results)
        p, q = args.p, args.q
        denominators = [[200*q] + [3*(4*p+q*(j == h)) for j in range(3)]
                        + [3*(3*p-q*(j == h)) for j in range(3)] for h in range(3)]
        numerators = [[0]+[6*q*(1+(j == h)) for j in range(3)]+[6*q]*3 for h in range(3)]
        for row in denominators:
            assert row[0] > sum(abs(v) for v in row[1:])
            assert all(v > 0 for v in row[1:]) or all(v < 0 for v in row[1:])
        record = {'replicas': [r['replicas'] for r in results], 'shift_numerator': p,
                  'shift_denominator': q, 'denominators': denominators, 'numerators': numerators,
                  'coordinates': 'z_j=(2*k_j-3*m)/(3*m), k_j counts ones in one of the six types',
                  'strict_scores': False,
                  'scope': 'Exact finite vanilla three-head upper certificates only; no lower-bound claim',
                  'verification': results}
        Path(args.write_certificate).write_text(json.dumps(record, indent=2)+'\n')


if __name__ == '__main__':
    main()
