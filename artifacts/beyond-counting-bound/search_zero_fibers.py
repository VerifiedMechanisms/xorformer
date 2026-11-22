"""Numerical search for regular zero-score fibers in the exact head model.

Every output is a numerical candidate or UNKNOWN. No optimization failure is
a nonexistence result. The common target is zero, unlike the nonzero-target
interpolation experiments in search_positive_fibers.py.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import least_squares


def score_and_jacobian(v, inputs, orientation, *, derivatives=False):
    """Evaluate the searched family, optionally returning its analytic Jacobian."""
    heads = len(orientation)
    n = inputs.shape[1]
    split = heads * n
    u = v[:split].reshape(heads, n)
    b = v[split:].reshape(heads, n)
    z = (inputs[:, None, :] * (1 - 2 * orientation)[None, :, None]
         + orientation[None, :, None])
    d = 1 + (z * b[None, :, :]).sum(axis=2)
    a = inputs @ u.T
    scores = 1 + (a / d).sum(axis=1)
    if not derivatives:
        return scores
    ju = inputs[:, None, :] / d[:, :, None]
    jb = -z * a[:, :, None] / d[:, :, None] ** 2
    jacobian = np.concatenate([ju.reshape(len(inputs), -1),
                               jb.reshape(len(inputs), -1)], axis=1)
    return scores, jacobian


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=10800)
    ap.add_argument('--trial-seconds', type=float, default=180)
    ap.add_argument('--seed', type=int, default=803182)
    ap.add_argument('--anchor', action='store_true',
                    help='Use p-1 zero scores and one nonzero held-out score.')
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    started = time.monotonic()
    deadline = started + args.seconds
    cases = [(6, 3), (7, 3), (7, 4), (8, 4), (8, 5), (9, 5)]
    trial = 0
    with (args.output / 'results.jsonl').open('a', buffering=1) as log:
        while time.monotonic() < deadline:
            n, heads = cases[trial % len(cases)]
            p = 2 * n * heads
            full = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
            indices = np.sort(rng.choice(np.arange(1, 1 << n), p, replace=False))
            x = full[indices]
            target = np.zeros(p)
            if args.anchor:
                target[-1] = -1 if trial % 2 else 1
            orientation = (np.arange(heads) % 2).astype(float)
            # Each denominator is 1 + sum of positive weights times either
            # x_i or (1-x_i), so it is strictly positive on the full cube.
            z = x[:, None, :] * (1 - 2 * orientation)[None, :, None] + orientation[None, :, None]

            def evaluate(v, inputs=x):
                return score_and_jacobian(v, inputs, orientation)

            def jac(v):
                return score_and_jacobian(v, x, orientation, derivatives=True)[1]

            b0 = np.exp(rng.uniform(-3, 3, (heads, n)))
            d0 = 1 + (z * b0[None, :, :]).sum(axis=2)
            design = (x[:, None, :] / d0[:, :, None]).reshape(p, -1)
            u0 = np.linalg.lstsq(design, target - 1, rcond=None)[0]
            v0 = np.r_[np.clip(u0, -999, 999), b0.ravel()]
            lo = np.r_[np.full(p // 2, -1000.), np.full(p // 2, 1e-4)]
            hi = np.r_[np.full(p // 2, 1000.), np.full(p // 2, 100.)]
            trial_started = time.monotonic()
            trial_deadline = min(deadline, trial_started + args.trial_seconds)
            latest = {'v': v0, 'evaluations': 0}

            class TrialTimeout(Exception):
                pass

            def residual(v):
                if time.monotonic() > trial_deadline:
                    raise TrialTimeout
                latest['v'] = v.copy()
                latest['evaluations'] += 1
                return evaluate(v) - target

            try:
                result = least_squares(residual, v0, jac=jac, bounds=(lo, hi),
                                       max_nfev=20000, ftol=1e-13, xtol=1e-13, gtol=1e-13)
                v = result.x
                termination = str(result.message)
            except TrialTimeout:
                v = latest['v']
                termination = 'trial deadline'
            values = evaluate(v) - target
            singular = np.linalg.svd(jac(v), compute_uv=False)
            rel = float(singular[-1] / singular[0])
            record = dict(trial=trial, n=n, heads=heads, sample_count=p,
                          zero_score_count=p - int(args.anchor),
                          anchor_target=float(target[-1]) if args.anchor else None,
                          residual=float(np.max(np.abs(values))),
                          smallest_singular=float(singular[-1]), relative_singular=rel,
                          evaluations=latest['evaluations'], termination=termination,
                          elapsed_seconds=time.monotonic() - trial_started,
                          status='UNKNOWN')
            if record['residual'] < 1e-10 and rel > 1e-8:
                name = f'candidate-{trial}.json'
                candidate = dict(record, indices=indices.tolist(), orientation=orientation.tolist(),
                                 targets=target.tolist(), parameters=v.tolist(),
                                 full_cube_scores=evaluate(v, full).tolist())
                (args.output / name).write_text(json.dumps(candidate, indent=2) + '\n')
                record.update(status='NUMERICAL_CANDIDATE', candidate=name)
            line = json.dumps(record)
            log.write(line + '\n')
            print(line, flush=True)
            trial += 1


if __name__ == '__main__':
    main()
