"""Search the explicit separating family at small replication counts.

The six group counts summarize 18*m input bits exactly. A successful integer
certificate is a three-head vanilla realization with slopes constant within
these groups. Search failure makes no lower-bound claim. Run with `heavy`.
The verifier uses exact integer arithmetic and the strict positive threshold.
Certificates have nonzero scores by default; `strict_scores: false` permits
zero scores for false labels, as in the unchanged model convention.
"""
import argparse
import itertools
import json
import math
from pathlib import Path
import time


def count_rows(m):
    return itertools.product(range(3 * m + 1), repeat=6)


def source_sign(m, counts):
    z = [2 * k - 3 * m for k in counts]
    d = [200 * m + z[h] - z[h + 3] for h in range(3)]
    a = [2 * (sum(z) + z[h]) for h in range(3)]
    value = sum(a[h] * math.prod(d[j] for j in range(3) if h != j) for h in range(3))
    return 1 if value > 0 else -1


def verify(record):
    m = record['replicas']
    assert type(m) is int and m > 0
    ds, ns = record['denominators'], record['numerators']
    strict = record.get('strict_scores', True)
    assert type(strict) is bool
    assert len(ds) == len(ns) == 3
    for row in ds + ns:
        assert len(row) == 7 and all(type(v) is int for v in row)
    for row in ds:
        assert row[0] > sum(abs(v) for v in row[1:])
        assert all(v > 0 for v in row[1:]) or all(v < 0 for v in row[1:])
    margin = None
    for counts in count_rows(m):
        z = [3 * m] + [2 * k - 3 * m for k in counts]
        d = [sum(a * b for a, b in zip(row, z)) for row in ds]
        n = [sum(a * b for a, b in zip(row, z)) for row in ns]
        value = sum(n[h] * math.prod(d[j] for j in range(3) if h != j) for h in range(3))
        signed = source_sign(m, counts) * value
        assert min(d) > 0, counts
        assert (value > 0) == (source_sign(m, counts) > 0), counts
        if strict:
            assert signed > 0, counts
        margin = signed if margin is None else min(margin, signed)
    return margin


def rationalize(m, result, Z, y):
    import numpy as np
    from scipy.optimize import linprog
    X = np.column_stack([np.ones(len(Z)), Z])
    B = np.array(result['B'])
    for scale in (10**6, 10**9, 10**12):
        ds = [[scale] + [int(round(v * scale)) for v in row] for row in B]
        if any(d[0] <= sum(abs(v) for v in d[1:]) or 0 in d[1:] for d in ds):
            continue
        D = X @ (np.array(ds, float) / scale).T
        F = np.column_stack([X * np.prod(np.delete(D, h, axis=1), axis=1)[:, None] for h in range(3)])
        U, s, V = np.linalg.svd(F, full_matrices=False)
        rank = int(sum(s > s[0] * 1e-12))
        lp = linprog(np.zeros(rank), A_ub=-y[:, None] * U[:, :rank],
                     b_ub=-np.ones(len(y)), bounds=[(None, None)] * rank, method='highs')
        if not lp.success:
            continue
        A = (V[:rank].T @ (lp.x / s[:rank])).reshape(3, 7)
        for numscale in (10**6, 10**9, 10**12, 10**15):
            ns = [[int(round(v * numscale)) for v in row] for row in A]
            record = {'replicas': m, 'input_bits': 18*m, 'denominators': ds, 'numerators': ns,
                      'coordinates': 'z_j=(2*k_j-3*m)/(3*m), k_j counts ones over all three blocks at group position j',
                      'scope': 'Exact vanilla upper certificate for this finite replication count only'}
            try:
                record['minimum_integer_margin'] = verify(record)
                return record
            except AssertionError:
                pass
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--replicas', type=int, default=1)
    parser.add_argument('--restarts', type=int, default=20)
    parser.add_argument('--maxiter', type=int, default=4000)
    parser.add_argument('--seed', type=int, default=2026112501)
    parser.add_argument('--verify')
    args = parser.parse_args()
    if args.verify:
        record = json.loads(Path(args.verify).read_text())
        print('Verified finite-family integer certificate, margin', verify(record), flush=True)
        return
    import numpy as np
    from search_many_head import fit
    m = args.replicas
    assert m > 0
    counts = list(count_rows(m))
    Z = (2 * np.array(counts, float) - 3*m) / (3*m)
    y = np.array([source_sign(m, row) for row in counts], float)
    start = time.monotonic()
    result = fit(Z, y, 3, args.restarts, np.random.default_rng(args.seed), args.maxiter)
    record = rationalize(m, result, Z, y) if result['status'] == 'floating_fit' else None
    out = {'replicas': m, 'seed': args.seed, 'restarts': args.restarts, 'maxiter': args.maxiter,
           'group_count_patterns': len(counts), 'result': result, 'seconds': time.monotonic()-start,
           'certified': record is not None}
    base = Path(__file__).parent / f'replicated_family_m{m}_{args.seed}'
    base.with_suffix('.json').write_text(json.dumps(out, indent=2)+'\n')
    if record:
        base.with_suffix('.exact.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'result'}), result['status'], flush=True)


if __name__ == '__main__':
    main()
