"""Adaptive parity-face discovery for the all-vanilla-three obstruction.

Numerical proposals only.  A discovered witness must subsequently receive
exact scalar admissibility and sign verification.  Failed scans are inconclusive.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

import numpy as np


N = 11
MASKS = np.arange(1 << N)
SPINS = 2 * ((MASKS[:, None] >> np.arange(N)) & 1) - 1
BITS = np.array(list(itertools.product([0, 1], repeat=3)))
PARITY = np.prod(2 * BITS - 1, axis=1)


def faces(axes):
    used = sum(axes)
    backgrounds = MASKS[(MASKS & used) == 0]
    return backgrounds[:, None] + BITS @ np.array(axes)


def best_face(labels, margins, axes, desired):
    candidates = faces(axes)
    good = np.all(labels[candidates] == desired, axis=1)
    if not np.any(good):
        return None
    selected = candidates[good]
    return selected[np.argmax(np.min(margins[selected], axis=1))].tolist()


def search(proposal, tolerance=1e-7):
    beta, numerator = np.array(proposal['beta']), np.array(proposal['numerators'])
    den = 1 + SPINS @ beta.T
    assert den.min() > 0
    scores = np.sum((numerator[:, 0] + SPINS @ numerator[:, 1:].T) / den, axis=1)
    labels, margins = np.sign(scores).astype(int), abs(scores)
    labels[margins <= tolerance] = 0
    diagnostics = {'strict_inputs': int(np.count_nonzero(labels)),
                   'ordinary_face_counts': [], 'candidate_partitions': 0,
                   'maximum_tied_columns': 0}
    for sign in [1, -1]:
        ordinary = {}
        for triple in itertools.combinations(range(N), 3):
            witness = best_face(labels, margins, [1 << i for i in triple], -sign * PARITY)
            if witness is not None:
                ordinary[triple] = witness
        diagnostics['ordinary_face_counts'].append(len(ordinary))
        if len(ordinary) < 30:
            continue
        for left in itertools.combinations(range(N), 6):
            rest = [i for i in range(N) if i not in left]
            tied = {}
            for pair in itertools.combinations(rest, 2):
                witness = best_face(labels, margins,
                                    [sum(1 << i for i in left)] + [1 << i for i in pair],
                                    sign * PARITY)
                if witness is not None:
                    tied[pair] = witness
            diagnostics['maximum_tied_columns'] = max(diagnostics['maximum_tied_columns'], len(tied))
            if len(tied) < 6:
                continue
            for middle in itertools.combinations(rest, 2):
                right = [i for i in rest if i not in middle]
                pairs = list(itertools.product(middle, right))
                if any(tuple(sorted(pair)) not in tied for pair in pairs):
                    continue
                bad = np.array([[tuple(sorted((i,) + pair)) not in ordinary
                                 for pair in pairs] for i in left])
                if max(bad.sum(axis=0).max(), bad.sum(axis=1).max()) > 1:
                    continue
                diagnostics['candidate_partitions'] += 1
                forced = [(r, c) for r in range(6) for c in range(6) if bad[r, c]]
                used_r, used_c = {r for r, _ in forced}, {c for _, c in forced}
                matching = forced + list(zip([r for r in range(6) if r not in used_r],
                                             [c for c in range(6) if c not in used_c]))
                matched = set(matching)
                entry_witnesses = [
                    {'row_coordinate': left[r], 'column_pair': pairs[c],
                     'masks': ordinary[tuple(sorted((left[r],) + pairs[c]))]}
                    for r in range(6) for c in range(6) if (r, c) not in matched]
                column_witnesses = [{'column_pair': pair, 'masks': tied[tuple(sorted(pair))]}
                                    for pair in pairs]
                masks = {m for w in entry_witnesses + column_witnesses for m in w['masks']}
                return diagnostics, {
                    'global_sign': sign, 'X': left, 'Y': middle, 'Z': right,
                    'matching': matching, 'entry_witnesses': entry_witnesses,
                    'column_witnesses': column_witnesses,
                    'minimum_float_margin': float(min(margins[list(masks)])),
                    'status': 'numerical witness only; exact certificate required'}
    return diagnostics, None


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='+', type=Path)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--tolerance', type=float, default=1e-7)
    args = ap.parse_args()
    for path in args.files:
        for index, line in enumerate(path.read_text().splitlines()):
            proposal = json.loads(line)
            if 'beta' not in proposal or 'numerators' not in proposal:
                continue
            start = time.time()
            diagnostic, witness = search(proposal, args.tolerance)
            result = {'source': str(path), 'index': index, **diagnostic,
                      'seconds': time.time() - start, 'witness': witness}
            with args.out.open('a') as out:
                out.write(json.dumps(result) + '\n')
            print(result, flush=True)
            if witness is not None:
                raise SystemExit(0)
