"""Search actual Boolean score fibers with binary active targets.

For a regular square active Jacobian J, test whether the multipliers for
minimizing the squared numerator norm have the required inequality signs.
No numerical result is an existence or nonexistence certificate. Sustained
runs must use heavy. This is a new constraint test, not a head lower bound.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import least_squares

from search_coordinate_score_fibers import check_gradient, score_jac


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--seconds', type=float, default=14400)
    p.add_argument('--seed', type=int, default=224171)
    p.add_argument('--max-evals', type=int, default=1800)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    print(json.dumps({'gradient_check': check_gradient()}), flush=True)
    rng = np.random.default_rng(args.seed)
    started = time.monotonic()
    deadline = started + args.seconds
    trial = 0
    regular = 0
    positive_dual = 0
    cases = [(6, 3), (7, 3), (7, 4)]
    class Expired(Exception):
        pass
    with (args.output / 'results.jsonl').open('a', buffering=1) as log:
        while time.monotonic() < deadline:
            n, h = cases[trial % len(cases)]
            size = 2 * n * h
            cube = ((np.arange(2 ** n)[:, None] >> np.arange(n)) & 1).astype(float)
            sample = np.sort(rng.choice(np.arange(1, 2 ** n), size, replace=False))
            x = cube[sample]
            theta = np.r_[rng.normal(-1, 2, n * h), rng.uniform(-3, 3, n * h)]
            if trial % 4 == 0:
                target = rng.choice((-1., 1.), size=size)
            else:
                value, _ = score_jac(theta, x, n, h)
                target = np.where(value >= np.median(value), 1., -1.)
            # Solve the linear numerator block before nonlinear refinement.
            b = np.exp(theta[n * h:].reshape(n, h))
            design = (x[:, :, None] / (1 + x @ b)[:, None, :]).reshape(size, n * h)
            theta[:n * h] = np.clip(np.linalg.lstsq(design, target - 1,
                                                   rcond=None)[0], -900, 900)
            cache = {}
            def evaluate(t):
                if time.monotonic() >= deadline:
                    raise Expired
                if 'theta' not in cache or not np.array_equal(t, cache['theta']):
                    v, j = score_jac(t, x, n, h)
                    cache.update(theta=t.copy(), residual=v-target, jac=j)
                return cache
            try:
                result = least_squares(lambda t: evaluate(t)['residual'], theta,
                    jac=lambda t: evaluate(t)['jac'],
                    bounds=(np.r_[np.full(n*h, -1e4), np.full(n*h, -10)],
                            np.r_[np.full(n*h, 1e4), np.full(n*h, 10)]),
                    x_scale='jac', max_nfev=args.max_evals,
                    ftol=1e-12, xtol=1e-12, gtol=1e-12)
                value, jac = score_jac(result.x, x, n, h)
                residual = float(np.max(np.abs(value - target)))
                singular = np.linalg.svd(jac, compute_uv=False)
                record = dict(trial=trial, n=n, heads=h, residual=residual,
                    min_singular=float(singular[-1]), nfev=int(result.nfev),
                    elapsed_seconds=time.monotonic()-started, status='UNKNOWN')
                if residual < 1e-8 and singular[-1] > 1e-8:
                    regular += 1
                    gradient = np.r_[2 * result.x[:n*h], np.zeros(n*h)]
                    multipliers = np.linalg.solve(jac.T, gradient) * target
                    record['min_signed_multiplier'] = float(multipliers.min())
                    record['positive_multipliers'] = int(np.count_nonzero(multipliers > 0))
                    full, _ = score_jac(result.x, cube, n, h)
                    remaining = np.setdiff1d(np.arange(1, 2 ** n), sample)
                    record['unsampled_min_abs_score'] = float(np.min(np.abs(full[remaining])))
                    record['unsampled_margin_violations'] = int(np.count_nonzero(
                        np.abs(full[remaining]) <= 1))
                    record['status'] = 'FLOATING_REGULAR_BINARY_FIBER'
                    name = f'candidate-{trial}.json'
                    data = dict(record, sample=sample.tolist(), target=target.tolist(),
                        theta=result.x.tolist(), multipliers=multipliers.tolist(),
                        full_scores=full.tolist(),
                        scope='numerical candidate only; all model coefficients remain unrestricted')
                    (args.output / name).write_text(json.dumps(data, indent=2)+'\n')
                    record['candidate'] = name
                    if multipliers.min() > 1e-8:
                        positive_dual += 1
                        record['status'] = 'FLOATING_POSITIVE_DUAL_CANDIDATE'
                log.write(json.dumps(record)+'\n')
                if 'candidate' in record or trial % 25 == 0:
                    print(json.dumps(record), flush=True)
            except Expired:
                break
            except (np.linalg.LinAlgError, FloatingPointError, ValueError) as exc:
                record = dict(trial=trial, n=n, heads=h, status='NUMERICAL_FAILURE_UNKNOWN',
                              error=type(exc).__name__, elapsed_seconds=time.monotonic()-started)
                log.write(json.dumps(record)+'\n')
            trial += 1
    print(json.dumps({'status':'SEARCH_FINISHED_UNKNOWN', 'trials':trial,
        'regular_binary_candidates':regular, 'positive_dual_candidates':positive_dual,
        'elapsed_seconds':time.monotonic()-started, 'target_proved':False}), flush=True)


if __name__ == '__main__':
    main()
