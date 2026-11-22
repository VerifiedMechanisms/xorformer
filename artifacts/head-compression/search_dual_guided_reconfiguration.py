#!/usr/bin/env python3
"""Try a pair replacement after feasible changes to the retained heads.

The pair-completion LP supplies a local objective for a retained-head LP.
Every accepted move is checked on the entire cube, and an improved
pair-completion objective is required. Only an independent integer audit
can produce a sign certificate. No convergence theorem is asserted.
Run with heavy.
"""
import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import sys
import time
for key in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[key] = '1'
import numpy as np
from scipy.optimize import linprog
from audit_pair_merges import integer_head
from audit_rational_score import audit

sys.set_int_max_str_digits(0)
LD = np.longdouble


def load_state(source):
    data = json.loads(source.read_text())
    n, heads = data['n'], len(data['heads'])
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(LD)
    plus = np.column_stack((np.ones(len(x), dtype=LD), x))
    minus = plus.copy(); minus[:, 1:] = 1 - minus[:, 1:]
    a, b, orientation = [], [], []
    for head in data['heads']:
        aa = np.array([LD(str(v)) for v in head['numerator']])
        bb = np.array([LD(str(v)) for v in head['denominator']])
        negative = np.all(bb[1:] < 0)
        if negative:
            aa = np.r_[aa.sum(), -aa[1:]]
            bb = np.r_[bb.sum(), -bb[1:]]
        assert bb[0] > 0 and np.all(bb[1:] >= 0)
        a.append(aa / bb[0]); b.append(bb / bb[0])
        orientation.append(-1 if negative else 1)
    a, b = np.array(a), np.array(b)
    orientation = np.array(orientation)
    pieces = np.zeros((len(x), heads), dtype=LD)
    for k in range(heads):
        z = plus if orientation[k] > 0 else minus
        pieces[:, k] = (z @ a[k]) / (z @ b[k])
    bias = LD(str(data['bias'][0])) / LD(str(data['bias'][1]))
    return data, plus, minus, a, b, orientation, pieces, bias


def complete_pair(score, pieces, pair, labels, z, seconds):
    residual = score - pieces[:, pair].sum(axis=1)
    scale = float(max(1, np.max(np.abs(residual))))
    rr = np.asarray(residual / scale, dtype=float)
    zz = np.asarray(z, dtype=float)
    n = zz.shape[1] - 1
    matrix = np.column_stack((-labels[:, None] * zz,
                              -(labels * rr)[:, None] * zz, np.ones(len(z))))
    fit = linprog(np.r_[np.zeros(2 * (n + 1)), -1.], A_ub=matrix,
        b_ub=np.zeros(len(z)), A_eq=np.r_[np.zeros(n + 1), np.ones(n + 1), 0.][None],
        b_eq=[1.], bounds=[(None, None)] * (n + 1) + [(1e-8, None)] * (n + 1) + [(None, 1.)],
        method='highs', options={'time_limit': seconds,
            'primal_feasibility_tolerance': 1e-10, 'dual_feasibility_tolerance': 1e-10})
    if fit.status != 0:
        return None
    u, beta = fit.x[:n + 1], fit.x[n + 1:2 * (n + 1)]
    if np.min(beta) <= 0:
        return None
    candidate = residual + LD(scale) * (z @ u.astype(LD)) / (z @ beta.astype(LD))
    weight = (-fit.ineqlin.marginals) * labels * (zz @ beta)
    weight /= max(1e-100, np.sum(np.abs(weight)))
    return {'slack': float(fit.x[-1]), 'a': LD(scale) * u.astype(LD),
            'b': beta.astype(LD), 'margin': float(np.min(labels * candidate)),
            'weight': weight, 'scale': scale}


def update_coordinates(score, piece, a, b, z, labels, weight, radius, seconds):
    denominator = z @ b
    t = np.asarray(z * b / denominator[:, None], dtype=float)
    # Each numerator feature is bounded by one, including the constant.
    numerator_scale = 1 + b
    numerator_scale[0] = 1
    j = np.asarray(z * numerator_scale / denominator[:, None], dtype=float)
    residual = score - piece
    scale = float(max(1, np.max(np.abs(piece)), np.max(np.abs(residual))))
    gamma = 0.25
    left_b = np.asarray((labels * residual - gamma) / scale, dtype=float)[:, None] * t
    left_a = labels[:, None] * j
    rhs = np.asarray((labels * score - gamma) / scale, dtype=float)
    objective = np.r_[(weight * np.asarray(piece / scale, dtype=float)) @ t, -(weight @ j)]
    norm = np.max(np.abs(objective))
    if norm < 1e-14:
        return None
    objective /= norm
    fit = linprog(objective, A_ub=-np.column_stack((left_b, left_a)), b_ub=rhs,
        bounds=[(-radius, radius)] * (2 * len(a)), method='highs',
        options={'time_limit': seconds, 'primal_feasibility_tolerance': 1e-10,
                 'dual_feasibility_tolerance': 1e-10})
    if fit.status != 0:
        return None
    delta, u = fit.x[:len(a)], fit.x[len(a):]
    return LD(scale) * numerator_scale * u.astype(LD), b * delta.astype(LD), float(-fit.fun)


def rational_head(a, b, orientation):
    aa = [Fraction(str(v)) for v in a]
    bb = [Fraction(str(v)) for v in b]
    if orientation < 0:
        aa = [sum(aa)] + [-v for v in aa[1:]]
        bb = [sum(bb)] + [-v for v in bb[1:]]
    return integer_head(aa, bb)


def export_candidate(data, a, b, orientation, pair, fit, replacement_orientation, out):
    candidate = {'n': data['n'], 'labels': data['labels'], 'bias': data['bias'],
        'heads': [rational_head(a[k], b[k], orientation[k]) for k in range(len(a)) if k not in pair]
                 + [rational_head(fit['a'], fit['b'], replacement_orientation)],
        'scope': 'One fixed truth table only; no universal theorem.'}
    path = out / 'candidate.json'; path.write_text(json.dumps(candidate) + '\n')
    report = audit(path, 224)
    if report['all_target_signs_certified']:
        path.rename(out / 'certificate.json')
        (out / 'certificate-audit.json').write_text(json.dumps(report, indent=2) + '\n')
        return True
    return False


def run(source, out, pair, replacement_orientation, seconds, seed):
    data, plus, minus, a, b, orientation, pieces, bias = load_state(source)
    score = bias + pieces.sum(axis=1)
    labels = np.array(data['labels'])
    assert np.min(labels * score) > 0.5
    zpair = plus if replacement_orientation > 0 else minus
    available = [k for k in range(len(a)) if k not in pair]
    rng = np.random.default_rng(seed)
    started = time.monotonic()
    current = complete_pair(score, pieces, pair, labels, zpair, 60)
    assert current is not None
    initial_slack = current['slack']
    accepted = attempts = 0
    certificate = False
    def save():
        np.savez_compressed(out / 'state.npz', a=a, b=b, orientation=orientation,
                            labels=labels, bias=bias, pair=np.array(pair),
                            replacement_orientation=replacement_orientation)
    while time.monotonic() - started < seconds and not (out / 'STOP').exists():
        if current['margin'] > 0.1:
            certificate = export_candidate(data, a, b, orientation, pair, current,
                                           replacement_orientation, out)
            if certificate:
                break
        if not available:
            break
        k = int(rng.choice(available))
        z = plus if orientation[k] > 0 else minus
        radius = (0.1, 0.3, 0.7)[attempts % 3]
        remaining = seconds - (time.monotonic() - started)
        if remaining <= 0:
            break
        proposal = update_coordinates(score, pieces[:, k], a[k], b[k], z, labels,
                                       current['weight'], radius, min(30, remaining))
        attempts += 1
        event = {'attempt': attempts, 'head': k, 'accepted': False,
                 'slack': current['slack'], 'seconds': time.monotonic() - started}
        if proposal is not None:
            da, db, gain = proposal
            event['linear_objective_gain'] = gain
            for step in (1., 0.5, 0.25, 0.125):
                aa, bb = a[k] + step * da, b[k] + step * db
                if np.min(bb) <= 0:
                    continue
                aa, bb = aa / bb[0], bb / bb[0]
                piece = (z @ aa) / (z @ bb)
                if np.max(np.abs(piece)) > 1e12:
                    continue
                trial_score = score + piece - pieces[:, k]
                if np.min(labels * trial_score) < 0.2:
                    continue
                remaining = seconds - (time.monotonic() - started)
                if remaining <= 0:
                    break
                trial_pieces = pieces.copy(); trial_pieces[:, k] = piece
                trial = complete_pair(trial_score, trial_pieces, pair, labels, zpair, min(30, remaining))
                if trial is None or trial['slack'] <= current['slack'] + 1e-12:
                    continue
                a[k], b[k], pieces[:, k] = aa, bb, piece
                # Recompute rather than accumulating update roundoff.
                score = bias + pieces.sum(axis=1)
                current = complete_pair(score, pieces, pair, labels, zpair, min(30, remaining))
                assert current is not None
                accepted += 1
                event.update(accepted=True, accepted_moves=accepted, step=step,
                    slack=current['slack'], pair_margin=current['margin'],
                    retained_score_margin=float(np.min(labels * score)))
                if accepted % 20 == 0:
                    save()
                break
        event['seconds'] = time.monotonic() - started
        with (out / 'events.jsonl').open('a') as stream:
            stream.write(json.dumps(event) + '\n')
        print(json.dumps(event), flush=True)
    save()
    result = {'seconds': time.monotonic() - started, 'attempts': attempts,
        'accepted_moves': accepted, 'initial_slack': initial_slack,
        'final_slack': current['slack'], 'pair_margin': current['margin'],
        'retained_score_margin': float(np.min(labels * score)),
        'certificate': 'certificate.json' if certificate else None,
        'scope': 'Numerical reconfiguration of one finite target; no convergence or universal bound.'}
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--pair', type=int, nargs=2, default=[7, 276])
    parser.add_argument('--orientation', type=int, choices=[-1, 1], default=-1)
    parser.add_argument('--seconds', type=float, default=21600)
    parser.add_argument('--seed', type=int, default=2026112222)
    args = parser.parse_args(); args.out.mkdir(parents=True, exist_ok=True)
    run(args.source, args.out, args.pair, args.orientation, args.seconds, args.seed)
