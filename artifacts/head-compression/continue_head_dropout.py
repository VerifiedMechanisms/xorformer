#!/usr/bin/env python3
"""Fade one frozen head, refitting survivors at each continuation stage.

This is a finite search, not a convergence theorem. Intermediate stages
still include the frozen head. A reduced certificate requires lambda = 0.
Run substantial instances through heavy.
"""
import argparse
import json
import os
from pathlib import Path
import time

for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
import scipy.linalg as la
import scipy.optimize as opt
from search_shared_affine_varpro import (
    features, geometry, initialize, unpack, exact_lift,
)
from audit_rational_score import audit


class StageEnd(Exception):
    pass


def residual_fit(yq, base, tolerance=1e-9, deadline=None):
    """Fit a score increment; base is 1 minus the current signed score."""
    # An absolute sub-nanoscopic gradient target is inappropriate when the
    # residual coordinates contain a large cancelling frozen contribution.
    tolerance = max(tolerance, 128*np.finfo(float).eps*la.norm(base))
    def objective(z):
        if deadline is not None and time.monotonic() >= deadline:
            raise StageEnd
        residual = np.maximum(base-yq@z, 0.)
        return .5*residual@residual, -yq.T@residual
    z = np.zeros(yq.shape[1])
    for iteration in range(500):
        value, gradient = objective(z)
        if np.max(np.abs(gradient)) < tolerance:
            break
        active = base-yq@z > 0
        qa = yq[active]
        gram = qa.T@qa
        gram.flat[::len(gram)+1] += 1e-12
        try:
            direction = la.solve(gram, -gradient, assume_a="pos", check_finite=False)
        except la.LinAlgError:
            direction = la.lstsq(gram, -gradient, cond=1e-13,
                                 lapack_driver="gelsy", check_finite=False)[0]
        slope, alpha = gradient@direction, 1.
        for _ in range(40):
            trial_value = objective(z+alpha*direction)[0]
            if trial_value <= value+1e-4*alpha*slope:
                break
            alpha *= .5
        z += alpha*direction
    value, gradient = objective(z)
    if np.max(np.abs(gradient)) > max(1e-8,tolerance):
        polished = opt.minimize(objective, z, jac=True, method="L-BFGS-B",
                               options={"maxiter":10000,"maxls":50,
                                        "ftol":1e-15,"gtol":tolerance,"maxcor":60})
        z = polished.x
        value, gradient = objective(z)
    return opt.OptimizeResult(x=z, fun=value, jac=gradient, nit=iteration+1)


def fixed_gradient(x, labels, logs, separation, coefficient, offset):
    units, n = logs.shape
    p, q, t1, t0, b, r = geometry(x, logs, separation)
    aa = coefficient[n+1:].reshape(units, n)
    ax = x@aa.T
    score = coefficient[0]+x@coefficient[1:n+1]+(ax*r).sum(axis=1)+offset
    residual = np.maximum(1-labels*score, 0.)
    weight = -labels*residual/len(x)
    z = weight[:, None]*ax*q/(b*b)
    glog = p*(p.sum(axis=1)[:, None]*(x.T@z).T-(z*t1).sum(axis=0)[:, None])
    gs = (weight[:, None]*ax*r*(2/(q+1)-2*q*t1/b)).sum(axis=0)
    return float(residual@residual/(2*len(x))), score, np.r_[glog.ravel(), gs]


class Stage:
    def __init__(self, labels, logs, separation, coefficient, offset, seconds, out):
        self.labels, self.units, self.n = labels, *logs.shape
        self.x = ((np.arange(len(labels))[:,None] >> np.arange(self.n)) & 1).astype(float)
        self.initial = np.r_[logs.ravel(), separation]
        self.previous, self.offset = coefficient.copy(), offset
        self.start, self.deadline = time.monotonic(), time.monotonic()+seconds
        self.out, self.best, self.success, self.events = out, None, None, []

    def objective(self, parameters):
        if time.monotonic() >= self.deadline or (self.out/"STOP").exists():
            raise StageEnd
        logs, separation = unpack(parameters, self.units, self.n)
        matrix = features(self.x, logs, separation)
        q, r = la.qr(matrix, mode="economic", check_finite=False)
        base_score = fixed_gradient(self.x, self.labels, logs, separation,
                                    self.previous, self.offset)[1]
        fit = residual_fit(self.labels[:,None]*q, 1-self.labels*base_score,
                           deadline=self.deadline)
        coefficient = self.previous+la.solve_triangular(r, fit.x, check_finite=False)
        loss, score, gradient = fixed_gradient(self.x, self.labels, logs, separation,
                                               coefficient, self.offset)
        self.previous = coefficient
        minimum = float((self.labels*score).min())
        event = dict(evaluation=len(self.events), seconds=time.monotonic()-self.start,
                     loss=loss, errors=int((self.labels*score<=0).sum()),
                     minimum_margin=minimum,
                     inner_gradient=float(np.max(np.abs(fit.jac))),
                     score_discrepancy=float(np.max(np.abs(score-base_score-q@fit.x))),
                     outer_gradient_norm=float(la.norm(gradient)))
        self.events.append(event)
        print(json.dumps(event), flush=True)
        state = (logs.copy(), separation.copy(), coefficient.copy())
        if self.best is None or loss < self.best[0]:
            self.best = (loss, state)
        if minimum > .25:
            self.success = state
            raise StageEnd
        return loss, gradient

    def run(self):
        try:
            opt.minimize(self.objective, self.initial, jac=True, method="L-BFGS-B",
                         bounds=[(-70,70)]*(self.units*self.n)+[(-35,35)]*self.units,
                         options={"maxiter":100000,"maxfun":100000,"maxls":40,
                                  "ftol":1e-15,"gtol":1e-10,"maxcor":50})
        except StageEnd:
            pass
        return self.success


def export_stage(labels, logs, separation, coefficient, frozen, scale):
    if scale == 0:
        return exact_lift(labels, logs, separation, coefficient)
    fl, fs, fa = frozen
    return exact_lift(labels, np.vstack((logs,fl)), np.r_[separation,fs],
                      np.r_[coefficient,scale*fa])


def run(checkpoint, out, unit, seconds, stage_seconds, initial_step):
    start = time.monotonic()
    labels, all_logs, all_s, all_c = initialize(checkpoint)
    units, n = all_logs.shape
    assert 0 <= unit < units
    x = ((np.arange(len(labels))[:,None] >> np.arange(n)) & 1).astype(float)
    margin = labels*(features(x, all_logs, all_s)@all_c)
    assert margin.min() > 0, "Continuation requires a strict starting score."
    all_c *= 2/float(margin.min())
    aa = all_c[n+1:].reshape(units,n)
    frozen = (all_logs[unit].copy(), float(all_s[unit]), aa[unit].copy())
    frozen_score = (x@frozen[2])*geometry(x, frozen[0][None,:], np.array([frozen[1]]))[-1][:,0]
    keep = np.arange(units) != unit
    logs, separation = all_logs[keep].copy(), all_s[keep].copy()
    coefficient = np.r_[all_c[:n+1],aa[keep].ravel()]
    scale, step, events = 1., initial_step, []
    while scale > 0 and time.monotonic()-start < seconds and not (out/"STOP").exists():
        trial_scale = max(0., scale-step)
        stage = Stage(labels, logs, separation, coefficient, trial_scale*frozen_score,
                      min(stage_seconds,seconds-(time.monotonic()-start)),out)
        state = stage.run()
        event = dict(stage=len(events), old_scale=scale, trial_scale=trial_scale,
                     seconds=time.monotonic()-start, evaluations=stage.events,
                     numerical_success=state is not None, accepted=False)
        if state is not None:
            cert, check = export_stage(labels, *state, frozen, trial_scale)
            event["exact_lift"] = check
            if cert is not None:
                directory = out/f"stage-{len(events):04d}"
                directory.mkdir()
                path = directory/"certificate.json"
                path.write_text(json.dumps(cert)+"\n")
                report = audit(path,224)
                (directory/"exact-audit.json").write_text(json.dumps(report,indent=2)+"\n")
                assert report["all_target_signs_certified"]
                logs, separation, coefficient = state
                scale, step = trial_scale, min(1.,step*2)
                np.savez(out/"continuation.npz",labels=labels,logs=logs,separation=separation,
                         coefficients=coefficient,frozen_logs=frozen[0],frozen_separation=frozen[1],
                         frozen_coefficients=frozen[2],frozen_scale=scale)
                event["accepted"] = True
                if scale == 0:
                    np.savez(out/"checkpoint.npz",labels=labels,logs=logs,separation=separation,
                             coefficients=coefficient,kind="shared-affine")
                    (out/"certificate.json").write_text(json.dumps(cert)+"\n")
                    (out/"exact-audit.json").write_text(json.dumps(report,indent=2)+"\n")
        if not event["accepted"]:
            step *= .5
        events.append(event)
        (out/"events.json").write_text(json.dumps(events,indent=2)+"\n")
        print(json.dumps({k:v for k,v in event.items() if k != "evaluations"}),flush=True)
        if step < 1e-12:
            break
    result = dict(seconds=time.monotonic()-start,frozen_scale=scale,
                  reduced_head_certificate=(out/"certificate.json").exists(),
                  scope="One finite truth table. Positive frozen scale does not reduce the head count.",
                  target_proved=False)
    (out/"result.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result),flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint",type=Path)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--unit",type=int,required=True)
    parser.add_argument("--seconds",type=float,default=36000)
    parser.add_argument("--stage-seconds",type=float,default=1200)
    parser.add_argument("--step",type=float,default=.01)
    args = parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    run(args.checkpoint,args.out,args.unit,args.seconds,args.stage_seconds,args.step)
