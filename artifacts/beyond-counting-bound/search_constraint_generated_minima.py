"""Numerator QP initialization and full-cube constraint generation.

Install Clarabel separately, or provide it on PYTHONPATH. This script uses its
standard convex-QP interface documented at clarabel.org. Solver results are
only floating candidates. Every minimum claim requires a separate certificate.
Run with heavy and single-thread BLAS on the shared machine.
"""
import argparse
import json
import time
from pathlib import Path

import clarabel
import numpy as np
from scipy import sparse
from scipy.linalg import qr
from scipy.optimize import minimize

from search_arithmetic_unit_minima import table, closest_negative
from search_full_cube_unit_minima import mixed_score_jac, check_mixed_gradient


def floating_sums(a):
    h, n = a.shape
    out = np.zeros((h, 1 << n))
    for i in range(n):
        k = 1 << i
        out[:, k:2*k] = out[:, :k] + a[:, i, None]
    return out


def full_table(theta, n, h, orientation):
    u = theta[:n*h].reshape(n, h).T
    p = np.exp(theta[n*h:].reshape(n, h).T)
    sums = floating_sums(p)
    den = 1 + sums
    for j in range(h):
        if orientation[j] < 0:
            den[j] = (1 + sums[j, ::-1]) / (1 + p[j].sum())
    return (floating_sums(u) / den).sum(axis=0)


def points(vertices, n):
    return ((vertices[:, None] >> np.arange(n)) & 1).astype(float)


def qp_numerators(theta, work, y, gamma, n, h, orientation):
    x = points(work, n)
    _, jac = mixed_score_jac(theta, x, n, h, orientation)
    G = y[work, None] * jac[:, :n*h]
    target = gamma * (y[work] < 0)
    settings = clarabel.DefaultSettings()
    settings.verbose = False
    settings.max_iter = 300
    settings.tol_feas = 1e-12
    settings.tol_gap_abs = 1e-12
    settings.tol_gap_rel = 1e-12
    settings.time_limit = 30.
    solver = clarabel.DefaultSolver(sparse.eye(n*h, format='csc'), np.zeros(n*h),
        sparse.csc_matrix(-G), -target, [clarabel.NonnegativeConeT(len(work))], settings)
    solution = solver.solve()
    result = theta.copy()
    if str(solution.status) in ('Solved', 'AlmostSolved'):
        result[:n*h] = np.array(solution.x)
    return result, str(solution.status)


def add_violations(work, slack, count=100):
    candidates = np.flatnonzero(slack < 0)
    candidates = candidates[candidates != 0]
    if len(candidates) > count:
        take = np.argpartition(slack[candidates], count-1)[:count]
        candidates = candidates[take]
    return np.unique(np.r_[work, candidates])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--seconds', type=float, default=21600)
    ap.add_argument('--trial-seconds', type=float, default=900)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seed', type=int, default=3081241)
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    start = time.monotonic()
    print(json.dumps({'status': 'DERIVATIVE_CHECK_PASS', 'error': check_mixed_gradient(),
                      'clarabel_version': clarabel.__version__}), flush=True)
    class Expired(Exception): pass
    trial = 0
    with (args.output/'results.jsonl').open('a', buffering=1) as log:
        while time.monotonic()-start < args.seconds:
            trial_start = time.monotonic()
            n, h = [(18, 3), (12, 3), (14, 3), (16, 3), (14, 4), (16, 4), (18, 4), (20, 3)][trial % 8]
            if trial == 0:
                data = json.loads((Path(__file__).parent/'integer-binary-fiber-18.json').read_text())
                U = np.array(data['numerator_scaled_slopes'], dtype=np.int64)
                weights = np.array(data['denominator_slopes'], dtype=np.int64)
                orientation = np.ones(h, dtype=np.int64)
            else:
                U = rng.integers(-12, 13, size=(h, n), dtype=np.int64)
                weights = rng.integers(1, 5, size=(h, n), dtype=np.int64)
                orientation = rng.choice([-1, 1], size=h)
                if trial % 3 == 0:
                    U[-1] = -U[:-1].sum(axis=0)
            den, num, D, P, constants = table(U, weights, orientation)
            found = closest_negative(P, D)
            if found is None or not np.any(P > 0):
                trial += 1
                continue
            gap, negative = found
            gamma = float(gap)/3
            y = np.where(P >= 0, 1., -1.)
            theta = np.r_[(U/(3*constants[:, None])).T.ravel(), np.log(weights).T.ravel()]
            values = full_table(theta, n, h, orientation)
            assert np.max(abs(values-P/(3*D))) < 1e-9
            test = np.array([1, 7, (1 << n)-1])
            assert np.max(abs(values[test]-(mixed_score_jac(theta, points(test, n), n, h, orientation)[0]-1))) < 1e-9
            zero = np.flatnonzero(P == 0)
            zero = zero[zero != 0]
            if len(zero) > 3*n*h:
                zero = np.sort(rng.choice(zero, 3*n*h, replace=False))
            work = np.unique(np.r_[zero, negative, rng.choice(np.arange(1,1 << n), 2*n*h, replace=False)])
            history = []
            try:
                def check_time():
                    if time.monotonic()-start > args.seconds or time.monotonic()-trial_start > args.trial_seconds:
                        raise Expired
                # Eliminate the easy numerator-only descent before joint work.
                for stage in range(40):
                    check_time()
                    theta, status = qp_numerators(theta, work, y, gamma, n, h, orientation)
                    slack = y*full_table(theta,n,h,orientation)-gamma*(y<0)
                    history.append(dict(phase='numerator_qp',stage=stage,status=status,
                                        work=len(work),relative_slack=float(slack.min()/gamma)))
                    if status not in ('Solved','AlmostSolved') or slack.min() >= -1e-7*gamma:
                        break
                    extended = add_violations(work, slack)
                    if len(extended) == len(work):
                        break
                    work = extended
                # Joint optimization sees a growing exact list of cube vertices.
                for stage in range(50):
                    check_time()
                    x = points(work,n)
                    norm_scale = max(1.,float(theta[:n*h]@theta[:n*h]))
                    cache = {}
                    def evaluate(t):
                        check_time()
                        if 'theta' not in cache or not np.array_equal(cache['theta'],t):
                            v,j=mixed_score_jac(t,x,n,h,orientation)
                            cache.update(theta=t.copy(),value=v-1,jac=j)
                        return cache
                    result=minimize(lambda t:.5*float(t[:n*h]@t[:n*h])/norm_scale, theta,
                        jac=lambda t:np.r_[t[:n*h]/norm_scale,np.zeros(n*h)],method='SLSQP',
                        bounds=[(None,None)]*(n*h)+[(-16.,16.)]*(n*h),
                        constraints=[dict(type='ineq',fun=lambda t:y[work]*evaluate(t)['value']-gamma*(y[work]<0),
                                          jac=lambda t:y[work,None]*evaluate(t)['jac'])],
                        options=dict(maxiter=1500,ftol=1e-13,disp=False))
                    theta=result.x
                    slack=y*full_table(theta,n,h,orientation)-gamma*(y<0)
                    rec=dict(phase='joint',stage=stage,solver_status=int(result.status),iterations=int(result.nit),
                             work=len(work),relative_slack=float(slack.min()/gamma),
                             norm=float(theta[:n*h]@theta[:n*h]),
                             boundary_distance=float(16-np.max(abs(theta[n*h:]))))
                    history.append(rec)
                    if slack.min() >= -1e-7*gamma:
                        active=np.flatnonzero(slack <= max(1e-10,1e-5*gamma))
                        active=active[active!=0]
                        if len(active)>=2*n*h and rec['boundary_distance']>1e-3:
                            _,jac=mixed_score_jac(theta,points(active,n),n,h,orientation)
                            signed=y[active,None]*jac
                            _,_,pivot=qr(signed.T,pivoting=True,mode='economic')
                            chosen=active[pivot[:2*n*h]]
                            matrix=signed[pivot[:2*n*h]]
                            sv=np.linalg.svd(matrix,compute_uv=False)
                            if sv[-1]>1e-9:
                                dual=np.linalg.solve(matrix.T,np.r_[theta[:n*h],np.zeros(n*h)])
                                candidate=dict(trial=trial,n=n,heads=h,gamma=gamma,theta=theta.tolist(),
                                    orientation=orientation.tolist(),labels=y.tolist(),active_vertices=chosen.tolist(),
                                    min_singular=float(sv[-1]),min_multiplier=float(dual.min()),multipliers=dual.tolist(),
                                    history=history,status='FLOATING_CANDIDATE_ONLY',main_target_proved=False)
                                name=f'candidate-{trial}-{stage}.json'
                                (args.output/name).write_text(json.dumps(candidate,indent=2)+'\n')
                                print(json.dumps(dict(trial=trial,candidate=name,min_multiplier=float(dual.min()))),flush=True)
                        break
                    extended=add_violations(work,slack)
                    if len(extended)==len(work):
                        break
                    work=extended
                record=dict(trial=trial,n=n,heads=h,gamma=gamma,status='UNKNOWN',history=history,
                            elapsed_seconds=time.monotonic()-start,trial_seconds=time.monotonic()-trial_start)
            except Expired:
                record=dict(trial=trial,n=n,heads=h,status='TIME_LIMIT_UNKNOWN',history=history,
                            elapsed_seconds=time.monotonic()-start,trial_seconds=time.monotonic()-trial_start)
            except (ValueError,np.linalg.LinAlgError,FloatingPointError) as error:
                record=dict(trial=trial,n=n,heads=h,status='NUMERICAL_FAILURE_UNKNOWN',error=str(error),
                            history=history,elapsed_seconds=time.monotonic()-start)
            log.write(json.dumps(record)+'\n')
            print(json.dumps({k:v for k,v in record.items() if k!='history'}),flush=True)
            trial+=1
    print(json.dumps(dict(status='FINISHED_UNKNOWN',trials=trial,elapsed_seconds=time.monotonic()-start,
                         main_target_proved=False)),flush=True)


if __name__=='__main__':
    main()
