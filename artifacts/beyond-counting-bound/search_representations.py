"""Adversarial search for admissible representations, never a lower-bound test.

Each successful numerical fit is rounded to rational parameters and checked on
the entire Boolean cube with exact integer interval arithmetic. Failure to fit
or to certify is recorded as UNKNOWN. Run sustained searches through `heavy`.
"""

import argparse
import hashlib
import json
import pathlib
import time

import numpy as np
from scipy.optimize import minimize


def cube(n):
    return ((np.arange(2**n, dtype=np.uint64)[:, None] >>
             np.arange(n, dtype=np.uint64)) & 1).astype(float)


def labels(x, family, seed):
    rng = np.random.default_rng(seed)
    if family == "random":
        return rng.choice([-1, 1], size=len(x))
    if family == "halfspace_product":
        n = x.shape[1]
        forms = (2*x-1) @ rng.normal(size=(n, n))
        forms += rng.normal(size=n)
        return np.prod(np.where(forms > 0, 1, -1), axis=1)
    if family == "random_code_subset":
        n = x.shape[1]
        k = int(np.ceil(np.log2(n+1)))
        check = ((np.arange(1, n+1)[:, None] >> np.arange(k)) & 1)
        in_code = np.all((x.astype(int) @ check) % 2 == 0, axis=1)
        return np.where(in_code & (rng.random(len(x)) < .5), 1, -1)
    raise ValueError(family)


def loss_gradient(v, x, y, orientation, sigma, regularizer=0.0):
    n = x.shape[1]
    h = len(orientation)
    u = v[:n*h].reshape(n, h)
    theta = v[n*h:].reshape(n, h)
    weights = np.exp(theta)
    # Positive or negative orientation, separately for each head.
    d = 1 + x @ (weights*(1-2*orientation)) + weights.sum(axis=0)*orientation
    a = x @ u
    score = sigma + np.sum(a/d, axis=1)
    residual = np.maximum(0, 1-y*score)
    loss = np.mean(residual**2) + regularizer*np.sum(u*u)
    ds = -2*y*residual/len(x)
    gu = x.T @ (ds[:, None]/d) + 2*regularizer*u
    gd = -ds[:, None]*a/(d*d)
    gw = (x.T @ gd)*(1-2*orientation) + gd.sum(axis=0)*orientation
    gt = gw*weights
    return loss, np.concatenate([gu.ravel(), gt.ravel()])


def exact_certificate(x, y, u, weights, orientation, sigma, bits=32, precision=128):
    """Check dyadic parameters without building enormous common denominators.

    For each rational term num/den, floor(2^precision*num/den) bounds the
    scaled term from below, and that integer plus one bounds it from above.
    All arithmetic in the final check uses Python integers.
    """
    scale, q = 2**bits, 2**precision
    wi = [[int(round(float(w)*scale)) for w in row] for row in weights.T]
    ui = [[int(round(float(a)*scale)) for a in row] for row in u.T]
    if any(w <= 0 for row in wi for w in row):
        return None
    floors_min = None
    for point, sign in zip(x.astype(int).tolist(), y.tolist()):
        lower = int(sigma)*q
        for wh, uh, orient in zip(wi, ui, orientation.tolist()):
            den = scale + sum(w*(1-b if orient else b) for w, b in zip(wh, point))
            num = sum(a*b for a, b in zip(uh, point))
            lower += (q*num)//den
        upper = lower+len(wi)
        signed_bound = lower if sign > 0 else -upper
        if signed_bound <= 0:
            return None
        floors_min = signed_bound if floors_min is None else min(floors_min, signed_bound)
    return {"parameter_bits":bits, "verification_precision":precision,
            "sigma":int(sigma), "orientation":orientation.astype(int).tolist(),
            "weights":wi, "numerators":ui,
            "minimum_scaled_margin_lower_bound":str(floors_min),
            "labels":y.astype(int).tolist()}


def fit(n, h, family, seed, restart, iterations):
    started = time.monotonic()
    x = cube(n)
    y = labels(x, family, seed)
    sigma = int(y[0])
    rng = np.random.default_rng(1000003*seed+7919*restart+97*n+31*h)
    orientation = (np.arange(h) % 2).astype(float)
    theta = rng.uniform(-4, 4, size=(n, h))
    weights = np.exp(theta)
    d = 1 + x @ (weights*(1-2*orientation)) + weights.sum(axis=0)*orientation
    features = (x[:, :, None]/d[:, None, :]).reshape(len(x), n*h)
    # This initialization is an approximate real fit, not a feasibility test.
    u = np.linalg.lstsq(features, y-sigma, rcond=1e-7)[0].reshape(n, h)
    initial = np.concatenate([u.ravel(), theta.ravel()])
    result = minimize(loss_gradient, initial,
                      args=(x, y, orientation, sigma), jac=True, method="L-BFGS-B",
                      bounds=[(None,None)]*(n*h)+[(-18,18)]*(n*h),
                      options={"maxiter":iterations, "ftol":1e-14,
                               "gtol":1e-10, "maxls":40, "maxcor":30})
    u = result.x[:n*h].reshape(n,h)
    weights = np.exp(result.x[n*h:].reshape(n,h))
    d = 1 + x @ (weights*(1-2*orientation)) + weights.sum(axis=0)*orientation
    score = sigma + np.sum((x @ u)/d, axis=1)
    margin = float(np.min(y*score))
    cert = exact_certificate(x,y,u,weights,orientation,sigma) if margin > 1e-7 else None
    record = {"n":n, "heads":h, "family":family, "seed":seed,
              "restart":restart, "iterations":int(result.nit),
              "loss":float(result.fun), "floating_min_margin":margin,
              "status":"CERTIFIED_REPRESENTATION" if cert else "UNKNOWN",
              "elapsed_seconds":time.monotonic()-started,
              "label_sha256":hashlib.sha256(y.astype(np.int8).tobytes()).hexdigest()}
    return record, cert


def check_gradient():
    x = cube(3)
    y = labels(x,"random",42)
    o = np.array([0.,1.])
    v = np.random.default_rng(0).normal(size=12)
    _, gradient = loss_gradient(v,x,y,o,int(y[0]))
    errors=[]
    for j in range(len(v)):
        step=np.zeros_like(v)
        step[j]=1e-5
        derivative=(loss_gradient(v+step,x,y,o,int(y[0]))[0]-
                    loss_gradient(v-step,x,y,o,int(y[0]))[0])/2e-5
        errors.append(abs(gradient[j]-derivative))
    assert max(errors)<1e-7, max(errors)
    # Check both orientations and both strict signs in the exact verifier.
    x1=cube(1)
    assert exact_certificate(x1,np.array([-1,1]),np.array([[4.]]),
                             np.array([[1.]]),np.array([0.]),-1)
    assert exact_certificate(x1,np.array([1,-1]),np.array([[-4.]]),
                             np.array([[1.]]),np.array([1.]),1)
    assert exact_certificate(x1,np.array([1,1]),np.array([[-4.]]),
                             np.array([[1.]]),np.array([1.]),1) is None
    print(json.dumps({"gradient_max_error":max(errors), "verifier_smoke_checks":"passed"}),flush=True)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--n",type=int,nargs="+",default=[7,8,9,10])
    parser.add_argument("--family",nargs="+",default=["random","halfspace_product","random_code_subset"])
    parser.add_argument("--restarts",type=int,default=4)
    parser.add_argument("--iterations",type=int,default=4000)
    parser.add_argument("--output",type=pathlib.Path,required=True)
    parser.add_argument("--check-only",action="store_true")
    args=parser.parse_args()
    check_gradient()
    if args.check_only:
        return
    args.output.mkdir(parents=True,exist_ok=True)
    with (args.output/"results.jsonl").open("a",buffering=1) as log:
        for n in args.n:
            sizes=sorted(set(max(1,int(np.ceil(c*2**n/n**2))) for c in [.5,1,2,3,4]))
            for family in args.family:
                for h in sizes:
                    for restart in range(args.restarts):
                        record,cert=fit(n,h,family,271828,restart,args.iterations)
                        if cert:
                            name=f"n{n}-h{h}-{family}-r{restart}.json"
                            (args.output/name).write_text(json.dumps(cert)+"\n")
                            record["certificate"]=name
                        line=json.dumps(record)
                        log.write(line+"\n")
                        print(line,flush=True)
                        if cert:
                            break


if __name__ == "__main__":
    main()
