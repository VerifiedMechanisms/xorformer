"""Search exact arithmetic zero layers followed by full-cube margin rescaling.

This is different from optimization over fixed random labels. Integer affine
fractions yield many exact zero values of T = S-1. Scale by twice the reciprocal
of the smallest negative magnitude. The zero layer is then active with label
+1 and the closest negative layer is active with label -1. All cube constraints
hold, by construction. A positive, full-rank exact KKT certificate would give
a strict local minimum of the squared normalized numerator norm.

Floating LP feasibility is only a candidate. Failure is not an impossibility
proof. No outcome of this finite search establishes the asymptotic target.
Run with heavy. Keep BLAS threads at one on the shared machine.
"""

import argparse
import json
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog


def subset_sums(rows):
    """Integer sums in binary vertex order, without storing the full cube."""
    h, n = rows.shape
    out = np.zeros((h, 1 << n), dtype=np.int64)
    for i in range(n):
        size = 1 << i
        out[:, size : 2 * size] = out[:, :size] + rows[:, i, None]
    return out


def table(u, weights, orientation):
    sums = subset_sums(weights)
    constants = np.where(orientation > 0, 1, 1 + weights.sum(axis=1))
    den = constants[:, None] + orientation[:, None] * sums
    num = subset_sums(u)
    prod = np.prod(den, axis=0)
    cleared = np.zeros(prod.shape, dtype=np.int64)
    for j in range(len(u)):
        cleared += num[j] * (prod // den[j])
    return den, num, prod, cleared, constants


def closest_negative(cleared, prod):
    """Floating shortlist, followed by an exact global integer comparison."""
    negative = np.flatnonzero(cleared < 0)
    if not len(negative):
        return None
    ratio = -cleared[negative] / prod[negative]
    v = int(negative[np.argmin(ratio)])
    gap = Fraction(-int(cleared[v]), int(prod[v]))
    # Product bounds are checked before this routine, so int64 is exact here.
    residual = -cleared[negative] * gap.denominator - prod[negative] * gap.numerator
    if residual.min() < 0:
        candidates = negative[residual < 0]
        v = min(candidates, key=lambda z: Fraction(-int(cleared[z]), int(prod[z])))
        gap = Fraction(-int(cleared[v]), int(prod[v]))
        residual = -cleared[negative] * gap.denominator - prod[negative] * gap.numerator
    assert residual.min() == 0
    return gap, negative[residual == 0]


def active_jacobian(vertices, u, den, num, constants, labels):
    h, n = u.shape
    x = ((vertices[:, None] >> np.arange(n)) & 1).astype(float)
    b = den[:, vertices].T.astype(float)
    a = num[:, vertices].T.astype(float)
    ju = np.concatenate([constants[j] * x / b[:, j, None] for j in range(h)], axis=1)
    jb = np.concatenate(
        [-constants[j] * x * a[:, j, None] / b[:, j, None] ** 2 for j in range(h)],
        axis=1,
    )
    return np.c_[ju, jb] * labels[:, None]


def self_check():
    u = np.array([[1, -3, 2], [2, 1, -2]], dtype=np.int64)
    w = np.array([[1, 2, 3], [3, 1, 2]], dtype=np.int64)
    ori = np.array([1, -1], dtype=np.int64)
    den, num, prod, p, constants = table(u, w, ori)
    for v in range(8):
        bits = [(v >> i) & 1 for i in range(3)]
        expected = sum(
            Fraction(sum(int(u[j, i]) * bits[i] for i in range(3)),
                     int(constants[j]) + int(ori[j]) * sum(int(w[j, i]) * bits[i] for i in range(3)))
            for j in range(2)
        )
        assert expected == Fraction(int(p[v]), int(prod[v]))
    vertices = np.arange(1, 8)
    jac = active_jacobian(vertices, u, den, num, constants, np.ones(7))
    normalized_u = u / constants[:, None]
    normalized_b = ori[:, None] * w / constants[:, None]
    theta = np.r_[normalized_u.ravel(), normalized_b.ravel()]
    x = ((vertices[:, None] >> np.arange(3)) & 1).astype(float)
    def score(t):
        return 1 + ((x @ t[:6].reshape(2, 3).T) / (1 + x @ t[6:].reshape(2, 3).T)).sum(axis=1)
    error = 0
    for j in range(12):
        delta = np.zeros(12)
        delta[j] = 1e-7
        error = max(error, float(np.max(abs((score(theta + delta) - score(theta - delta)) / 2e-7 - jac[:, j]))))
    assert error < 1e-6
    return error


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seconds', type=float, default=21600)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seed', type=int, default=73940123)
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    print(json.dumps({'status': 'SELF_CHECK_PASS', 'derivative_error': self_check()}), flush=True)
    rng = np.random.default_rng(args.seed)
    start = time.monotonic()
    trial = 0
    candidates = 0
    last_report = start
    with (args.output / 'results.jsonl').open('a', buffering=1) as log:
        while time.monotonic() - start < args.seconds:
            n, h = [(18, 3), (20, 3), (22, 3), (20, 4), (22, 4), (24, 3)][trial % 6]
            mode = (trial // 6) % 4
            w = rng.integers(1, 5, size=(h, n), dtype=np.int64)
            u = rng.integers(-12, 13, size=(h, n), dtype=np.int64)
            if mode == 1:
                u[-1] = -u[:-1].sum(axis=0)
            elif mode == 2:
                u -= int(round(u.mean()))
            elif mode == 3:
                w = rng.integers(1, 4, size=(1, n), dtype=np.int64) + rng.integers(0, 2, size=(h, n), dtype=np.int64)
                u[-1] = -u[:-1].sum(axis=0)
            ori = np.ones(h, dtype=np.int64) if trial % 2 else rng.choice([-1, 1], size=h)
            den, num, prod, p, constants = table(u, w, ori)
            bound_p = sum(int(abs(u[j]).sum()) * int(np.prod(1 + w.sum(axis=1)) // (1 + w[j].sum())) for j in range(h))
            bound_d = int(np.prod(1 + w.sum(axis=1)))
            # This also certifies all integer products in closest_negative.
            assert 2 * bound_p * bound_d < np.iinfo(np.int64).max
            zeros = np.flatnonzero(p == 0)
            zeros = zeros[zeros != 0]
            record = dict(trial=trial, n=n, heads=h, mode=mode, orientation=ori.tolist(),
                          zero_count=len(zeros), status='UNKNOWN', elapsed_seconds=time.monotonic() - start)
            if len(zeros) >= 2 * n * h - 1:
                closest = closest_negative(p, prod)
                if closest is not None:
                    gap, negative = closest
                    active = np.r_[zeros, negative]
                    y = np.r_[np.ones(len(zeros)), -np.ones(len(negative))]
                    J = active_jacobian(active, u, den, num, constants, y)
                    normalized_u = (u / constants[:, None]).ravel()
                    norm = float(normalized_u @ normalized_u)
                    rhs = np.r_[normalized_u * (float(gap) / norm), np.zeros(n * h)]
                    # Normalize the total multiplier on the closest negative layer to one.
                    E = np.vstack([J.T, np.r_[np.zeros(len(zeros)), np.ones(len(negative))]])
                    rhs = np.r_[rhs, 1.]
                    row_scale = np.maximum(np.max(abs(E), axis=1), abs(rhs))
                    row_scale[row_scale == 0] = 1
                    result = linprog(np.zeros(len(active)), A_eq=E / row_scale[:, None],
                                     b_eq=rhs / row_scale, bounds=(0, None), method='highs',
                                     options={'dual_feasibility_tolerance': 1e-9,
                                              'primal_feasibility_tolerance': 1e-9,
                                              'time_limit': 120.})
                    record.update(gap=str(gap), negative_active=len(negative), lp_status=int(result.status))
                    if result.success:
                        positive = np.flatnonzero(result.x > 1e-9)
                        rank = int(np.linalg.matrix_rank(J[positive], tol=1e-9))
                        record.update(status='FLOATING_KKT_CANDIDATE', positive_support=len(positive),
                                      support_rank=rank, residual=float(np.max(abs(E @ result.x - rhs))))
                        data = dict(record, numerator_integer=u.tolist(), denominator_weights=w.tolist(),
                                    denominator_constants=constants.tolist(), active_vertices=active.tolist(),
                                    labels=y.tolist(), multipliers=result.x.tolist(), main_target_proved=False)
                        filename = f'candidate-{trial}.json'
                        (args.output / filename).write_text(json.dumps(data, indent=2) + '\n')
                        record['candidate'] = filename
                        candidates += 1
            log.write(json.dumps(record) + '\n')
            if trial == 0 or time.monotonic() - last_report >= 55 or 'candidate' in record:
                print(json.dumps(record), flush=True)
                last_report = time.monotonic()
            trial += 1
    print(json.dumps(dict(status='SEARCH_FINISHED_UNKNOWN', trials=trial, candidates=candidates,
                          elapsed_seconds=time.monotonic() - start, main_target_proved=False)), flush=True)


if __name__ == '__main__':
    main()
