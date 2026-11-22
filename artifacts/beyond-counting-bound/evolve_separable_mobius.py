"""Adversarial finite search for scalar positive-denominator sign patterns.

Every retained witness is independently checked over rational numbers. A failed
search is UNKNOWN, never a VC-dimension upper bound or a head lower bound.
"""
import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import time

import numpy as np


def verify(record):
    poles = [[Fraction(str(v)) for v in row] for row in record['poles']]
    residues = [[Fraction(str(v)) for v in row] for row in record['residuals']]
    thresholds = [Fraction(str(v)) for v in record['thresholds']]
    assert all(v > 0 for row in poles for v in row)
    minimum = None
    for mask, point in record['witnesses'].items():
        point = [Fraction(str(v)) for v in point]
        assert all(v > 0 for v in point)
        values = [sum(r / (x + p) for r, x, p in zip(rr, point, pp)) - c
                  for rr, pp, c in zip(residues, poles, thresholds)]
        assert all(v != 0 for v in values)
        assert sum(1 << j for j, v in enumerate(values) if v > 0) == int(mask)
        m = min(abs(v) for v in values)
        minimum = m if minimum is None else min(m, minimum)
    record['exact_rational_verified'] = True
    record['minimum_absolute_value'] = str(minimum)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=3600)
    ap.add_argument('--grid', type=int, default=31)
    ap.add_argument('--seed', type=int, default=15592026)
    args = ap.parse_args()
    source = json.loads(args.source.read_text())
    poles = np.array(source['poles'])
    residues = np.array(source['residuals'])
    thresholds = np.array(source['thresholds'])
    queries, heads = poles.shape
    rng = np.random.default_rng(args.seed)
    points = np.array(list(itertools.product(np.geomspace(.0001, 10000, args.grid),
                                            repeat=heads)))
    points = np.concatenate([points, np.array(list(source['witnesses'].values()))])
    bits = 1 << np.arange(queries, dtype=np.uint64)

    def values(p, r, c):
        return (r[None, :, :] / (points[:, None, :] + p)).sum(axis=2) - c

    scores = values(poles, residues, thresholds)
    masks = ((scores > 0).astype(np.uint64) * bits).sum(axis=1)
    count = len(np.unique(masks))
    best_count = -1
    best = None
    start = time.monotonic()
    step = 0
    while time.monotonic() - start < args.seconds:
        if count > best_count:
            unique, indices = np.unique(masks, return_index=True)
            best = dict(poles=poles.tolist(), residuals=residues.tolist(),
                        thresholds=thresholds.tolist(), step=step,
                        patterns=count, total_patterns=2**queries,
                        witnesses={str(int(m)): points[i].tolist()
                                   for m, i in zip(unique, indices)},
                        elapsed_seconds=time.monotonic() - start,
                        status='FINITE_WITNESSES_ONLY')
            verify(best)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(best, indent=2) + '\n')
            best_count = count
            print(json.dumps({k: best[k] for k in ['step', 'patterns',
                             'total_patterns', 'elapsed_seconds']}), flush=True)
            if count == 2**queries:
                break
        q = int(rng.integers(queries))
        pp = poles[q].copy()
        rr = residues[q].copy()
        cc = thresholds[q]
        scale = rng.choice([.01, .05, .2, .5, 1.5])
        kind = rng.integers(4)
        if kind in [0, 2]:
            pp *= np.exp(rng.normal(size=heads) * scale)
        if kind in [1, 2]:
            rr += rng.normal(size=heads) * scale * (np.abs(rr) + pp * .01)
        vv = (rr[None, :] / (points + pp)).sum(axis=1)
        if kind == 3:
            cc = float(np.quantile(vv, rng.uniform(.01, .99)))
        else:
            cc += float(rng.normal() * scale * np.std(vv))
        row = vv - cc
        new_masks = (masks & ~bits[q]) | ((row > 0).astype(np.uint64) * bits[q])
        new_count = len(np.unique(new_masks))
        temperature = .08 if step % 1000 < 900 else .8
        if new_count >= count or rng.random() < np.exp((new_count-count)/temperature):
            poles[q], residues[q], thresholds[q] = pp, rr, cc
            scores[:, q] = row
            masks, count = new_masks, new_count
        step += 1
        if step % 5000 == 0 and count < best_count:
            poles, residues, thresholds = (np.array(best[k]) for k in
                                          ['poles', 'residuals', 'thresholds'])
            scores = values(poles, residues, thresholds)
            masks = ((scores > 0).astype(np.uint64) * bits).sum(axis=1)
            count = len(np.unique(masks))
    print(json.dumps({'finished': True, 'best': best_count, 'steps': step,
                      'seconds': time.monotonic()-start,
                      'failure_status': 'UNKNOWN'}), flush=True)


if __name__ == '__main__':
    main()
