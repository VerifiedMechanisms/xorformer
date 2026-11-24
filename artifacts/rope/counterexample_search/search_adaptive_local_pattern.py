"""Find orientation-obstructing local witnesses in proposed pure-four scores.

This is a floating-point discovery tool.  A reported match still requires exact
pure admissibility, exact orbit signs, and a lower-bound proof for its witness.
Coordinates are selector first, then sixteen spatial coordinates.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

import numpy as np


N = 16
FULL = (1 << N) - 1
MASKS = np.arange(1 << N, dtype=np.int64)
SPINS = 2 * ((MASKS[:, None] >> np.arange(N)) & 1) - 1
FLIPS = 1 << np.arange(N)
CENTERS = np.array([mask for mask in range(1 << N)
                    if mask in (0, FULL) or mask.bit_count() == 8], dtype=np.int64)


def orbit_labels(proposal, tolerance):
    beta = np.array(proposal['beta'])
    numerator = np.array(proposal['numerators'])
    scores = []
    for selector in [-1, 1]:
        den = 1 + selector * beta[:, 0] + SPINS @ beta[:, 1:].T
        num = numerator[:, 0] + selector * numerator[:, 1] + SPINS @ numerator[:, 2:].T
        assert den.min() > 0
        scores.append(np.sum(num / den, axis=1))
    signs = np.sign(scores[1]).astype(np.int8)
    margins = np.minimum.reduce([signs * scores[1], -signs * scores[0],
                                 signs * scores[1][::-1], -signs * scores[0][::-1]])
    signs[margins <= tolerance] = 0
    return signs, margins


def middle_witnesses(labels, center, right, base_label):
    witnesses = []
    for j in right:
        others = [i for i in right if i != j]
        all_others = sum(1 << i for i in others)
        match = None
        # A background and its complement are the same four-point witness.
        for bits in range(1 << (len(others) - 1)):
            mask = sum((1 << i) for k, i in enumerate(others) if bits >> k & 1)
            masks = [center ^ mask, center ^ mask ^ (1 << j),
                     center ^ mask ^ all_others,
                     center ^ mask ^ all_others ^ (1 << j)]
            if all(labels[m] == y for m, y in
                   zip(masks, [-base_label, base_label, -base_label, base_label])):
                match = {'coordinate': j, 'background_flip_mask': mask,
                         'spatial_masks': masks}
                break
        if match is None:
            return None
        witnesses.append(match)
    return witnesses


def search(proposal, tolerance=1e-7):
    labels, margins = orbit_labels(proposal, tolerance)
    center_labels = labels[CENTERS]
    good = (center_labels != 0) & np.all(
        labels[CENTERS[:, None] ^ FLIPS[None, :]] == -center_labels[:, None], axis=1)
    centers = CENTERS[good]
    neighbor_counts = np.sum(labels[CENTERS[:, None] ^ FLIPS[None, :]] ==
                             -center_labels[:, None], axis=1)
    neighbor_counts[center_labels == 0] = -1
    nearest = np.argsort(-neighbor_counts)[:4]
    diagnostics = {'consistent_spatial_inputs': int(np.count_nonzero(labels)),
                   'eligible_centers': len(centers), 'cross_partitions': 0,
                   'nearest_centers': [{'mask': int(CENTERS[i]),
                                        'opposite_neighbors': int(neighbor_counts[i]),
                                        'base_label': int(center_labels[i])}
                                       for i in nearest]}
    for center in centers:
        base_label = int(labels[center])
        bad = labels[int(center) ^ FLIPS[:, None] ^ FLIPS[None, :]] != base_label
        if center in (0, FULL):
            # Symmetry between blocks lets coordinate zero belong to the left.
            partitions = ([0] + list(rest) for rest in itertools.combinations(range(1, N), 7))
        else:
            plus = [i for i in range(N) if center >> i & 1]
            minus = [i for i in range(N) if not center >> i & 1]
            partitions = [plus, minus]
        for left in partitions:
            right = [i for i in range(N) if i not in left]
            cross = bad[np.ix_(left, right)]
            if max(cross.sum(axis=0).max(), cross.sum(axis=1).max()) > 1:
                continue
            diagnostics['cross_partitions'] += 1
            for first, second in [(left, right), (right, left)]:
                middle = middle_witnesses(labels, int(center), second, base_label)
                if middle is None:
                    continue
                forced = [(first[i], second[j]) for i in range(8) for j in range(8)
                          if bad[first[i], second[j]]]
                used_left = {a for a, _ in forced}
                used_right = {b for _, b in forced}
                matching = forced + list(zip([i for i in first if i not in used_left],
                                             [j for j in second if j not in used_right]))
                masks = {int(center)} | {int(center) ^ (1 << i) for i in range(N)}
                matched = set(matching)
                masks |= {int(center) ^ (1 << i) ^ (1 << j)
                          for i in first for j in second if (i, j) not in matched}
                masks |= {m for witness in middle for m in witness['spatial_masks']}
                return diagnostics, {'center': int(center), 'base_label': base_label,
                    'left': first, 'right': second, 'matching': matching, 'middle': middle,
                    'minimum_float_orbit_margin': float(min(margins[list(masks)])),
                    'status': 'floating witness only; exact certification required'}
    return diagnostics, None


def search_arbitrary_faces(proposal, tolerance=1e-7):
    """Each negative cross coefficient may use its own parity-face witness."""
    labels, margins = orbit_labels(proposal, tolerance)
    diagnostics = {'consistent_spatial_inputs': int(np.count_nonzero(labels)),
                   'negative_pair_counts': [], 'cross_partitions': 0,
                   'maximum_middle_columns': 0}
    for global_sign in [1, -1]:
        witnesses = {}
        negative = np.zeros((N, N), dtype=bool)
        for i in range(N):
            for j in range(i):
                bases = MASKS[((MASKS >> i) & 1 == 0) & ((MASKS >> j) & 1 == 0)]
                masks = np.array([bases, bases ^ (1 << i), bases ^ (1 << j),
                                  bases ^ (1 << i) ^ (1 << j)]).T
                desired = global_sign * np.array([-1, 1, 1, -1])
                valid = np.all(labels[masks] == desired, axis=1)
                if not np.any(valid):
                    continue
                choices = masks[valid]
                choice = choices[np.argmax(np.min(margins[choices], axis=1))]
                witnesses[i, j] = choice.tolist()
                negative[i, j] = negative[j, i] = True
        diagnostics['negative_pair_counts'].append(int(negative.sum() // 2))
        for rest in itertools.combinations(range(1, N), 7):
            left = [0] + list(rest)
            right = [i for i in range(N) if i not in left]
            bad = ~negative[np.ix_(left, right)]
            if max(bad.sum(axis=0).max(), bad.sum(axis=1).max()) > 1:
                continue
            diagnostics['cross_partitions'] += 1
            for first, second in [(left, right), (right, left)]:
                middle = middle_witnesses(labels, 0, second, -global_sign)
                if middle is None:
                    continue
                forced = [(i, j) for i in first for j in second if not negative[i, j]]
                used_left = {a for a, _ in forced}
                used_right = {b for _, b in forced}
                matching = forced + list(zip([i for i in first if i not in used_left],
                                             [j for j in second if j not in used_right]))
                matched = set(matching)
                faces = [{'coordinates': [i, j],
                          'spatial_masks': witnesses[max(i, j), min(i, j)]}
                         for i in first for j in second if (i, j) not in matched]
                masks = {m for face in faces for m in face['spatial_masks']}
                masks |= {m for witness in middle for m in witness['spatial_masks']}
                return diagnostics, {'global_sign': global_sign, 'left': first,
                    'right': second, 'matching': matching, 'middle': middle,
                    'negative_cross_faces': faces,
                    'minimum_float_orbit_margin': float(min(margins[list(masks)])),
                    'status': 'floating arbitrary-face witness; exact certification required'}
    return diagnostics, None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('files', nargs='+', type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--tolerance', type=float, default=1e-7)
    parser.add_argument('--all-selectors', action='store_true')
    parser.add_argument('--arbitrary-faces', action='store_true')
    args = parser.parse_args()
    for path in args.files:
        for index, line in enumerate(path.read_text().splitlines()):
            proposal = json.loads(line)
            if 'beta' not in proposal or 'numerators' not in proposal:
                continue
            for selector in (range(17) if args.all_selectors else [0]):
                order = [selector] + [i for i in range(17) if i != selector]
                changed = {**proposal,
                    'beta': np.array(proposal['beta'])[:, order].tolist(),
                    'numerators': np.array(proposal['numerators'])[:,
                                      [0] + [i + 1 for i in order]].tolist()}
                start = time.time()
                diagnostics, witness = (search_arbitrary_faces if args.arbitrary_faces
                                        else search)(changed, args.tolerance)
                result = {'source': str(path), 'index': index, 'restart': proposal.get('restart'),
                          'selector': selector, 'coordinate_order': order,
                          **diagnostics, 'seconds': time.time() - start, 'witness': witness}
                with args.out.open('a') as output:
                    output.write(json.dumps(result) + '\n')
                print(result, flush=True)
                if witness:
                    return


if __name__ == '__main__':
    main()
