"""Search the consistent 102-point cubic lower-bound pattern.

The unrestricted fixed-beta LP includes every pure numerator at that beta.
Optimization failures have no lower-bound meaning.
"""
import itertools
from pathlib import Path
import sys
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'four_head_middle'))
import search_fixed_denominator_lp as lp


def pattern():
    points = {}
    def add(x, label):
        key = tuple(x)
        assert key not in points or points[key] == label
        points[key] = label
    pairs = list(itertools.product(range(6, 8), range(8, 11)))
    for i in range(6):
        for col, (j, k) in enumerate(pairs):
            if i == col:
                continue
            for bits in itertools.product([-1, 1], repeat=3):
                x = -np.ones(11, dtype=int)
                x[[i, j, k]] = bits
                add(x, -np.prod(bits))
    for j, k in pairs:
        for bits in itertools.product([-1, 1], repeat=3):
            x = np.ones(11, dtype=int)
            x[:6] = bits[0]; x[j] = bits[1]; x[k] = bits[2]
            add(x, np.prod(bits))
    assert len(points) == 102
    return np.array(list(points)), np.array(list(points.values()))


if __name__ == '__main__':
    hard_mode = None
    if '--hard-parity' in sys.argv:
        sys.argv.remove('--hard-parity'); hard_mode = 'parity'
    if '--hard-shared' in sys.argv:
        sys.argv.remove('--hard-shared'); hard_mode = 'shared'
    if '--hard-anchors' in sys.argv:
        sys.argv.remove('--hard-anchors'); hard_mode = 'anchors'
    if '--hard-columns' in sys.argv:
        sys.argv.remove('--hard-columns'); hard_mode = 'columns'
    if '--hard-both' in sys.argv:
        sys.argv.remove('--hard-both'); hard_mode = 'both'
    lp.Z, lp.Y = pattern()
    lp.X = np.c_[np.ones(len(lp.Z)), lp.Z]
    lp.N, lp.H = 11, 3
    lp.NV = lp.H * (lp.N + 1)
    lp.ELL, lp.K, lp.BASE = lp.NV, lp.NV + lp.H, lp.NV + 2 * lp.H
    if hard_mode == 'parity':
        # The first off-diagonal parity face uses X0,Y0,Z1.
        other = [i for i in range(11) if i not in [0,6,9]]
        lp.HARD_MASK = np.all(lp.Z[:,other] == -1, axis=1)
    if hard_mode == 'shared':
        # Shared low-weight vertices are the easy-to-sacrifice bottleneck.
        lp.HARD_MASK = np.sum(lp.Z == 1, axis=1) <= 2
    if hard_mode == 'anchors':
        other = [i for i in range(11) if i not in [0,6,9]]
        lp.HARD_MASK = np.all(lp.Z[:,other] == -1, axis=1) | np.all(lp.Z == 1, axis=1)
    if hard_mode == 'columns':
        lp.HARD_MASK = np.all(lp.Z[:,:6] == lp.Z[:,0,None], axis=1) & (
            np.sum(lp.Z[:,6:8] == -1, axis=1) <= 1) & (
            np.sum(lp.Z[:,8:11] == -1, axis=1) <= 1)
    if hard_mode == 'both':
        other = [i for i in range(11) if i not in [0,6,9]]
        ordinary = np.all(lp.Z[:,other] == -1,axis=1)
        column = np.all(lp.Z[:,:6] == lp.Z[:,0,None],axis=1) & np.all(lp.Z[:,[7,9,10]]==1,axis=1)
        lp.HARD_MASK = ordinary | column
    lp.main()
