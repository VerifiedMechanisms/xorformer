#!/usr/bin/env python3
"""Search signs in logarithmic positive/negative contribution coordinates.

The mathematical score is still an admissible affine-ratio sum. Logarithms
only evaluate and optimize its sign stably; they are not additional model
operations. Success requires independent exact integer verification. Use heavy.
"""
import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import time

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import numpy as np
import torch
from search_sign_scores import exact_check, integer_pair

torch.set_num_threads(1)


def log_difference(a, b, bias, active, signs):
    denominator = torch.logsumexp(b[None].masked_fill(~active, -torch.inf), dim=2)
    terms = a[None]-denominator[:, :, None]
    positive = terms.masked_fill(~(active & (signs[None] > 0)), -torch.inf)
    negative = terms.masked_fill(~(active & (signs[None] < 0)), -torch.inf)
    plus = torch.logsumexp(torch.cat((bias[0].expand(len(active), 1),
                                      positive.flatten(1)), dim=1), dim=1)
    minus = torch.logsumexp(torch.cat((bias[1].expand(len(active), 1),
                                       negative.flatten(1)), dim=1), dim=1)
    return plus-minus


def export(n, y, a, b, bias, signs, orientation):
    bmax = b.max(axis=1)
    shift = max(float((a-bmax[:, None]).max()), float(bias.max()))
    heads = []
    for ah, bh, sg, ori, bs in zip(a, b, signs, orientation, bmax):
        aa = sg*np.exp(ah-bs-shift)
        bb = np.exp(bh-bs)
        assert np.isfinite(aa).all() and (bb > 0).all()
        ai, bi = integer_pair(aa, bb)
        if ori < 0:
            # Convert the already exact binary rationals from the 1-x chart.
            ai = [sum(ai)] + [-v for v in ai[1:]]
            bi = [sum(bi)] + [-v for v in bi[1:]]
        heads.append({"numerator": ai, "denominator": bi})
    bc = (Fraction(float(np.exp(bias[0]-shift))) -
          Fraction(float(np.exp(bias[1]-shift))))
    return {"n": n, "labels": y.astype(int).tolist(), "heads": heads,
            "bias": [bc.numerator, bc.denominator],
            "scope": "This finite truth table only; no universal theorem."}


def smoke_check():
    rng = np.random.default_rng(450000)
    n, h = 3, 4
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    orientation = rng.choice([-1, 1], h)
    t = np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None])
    z = np.concatenate((np.ones((len(x), h, 1)), t), axis=2)
    a, b = rng.normal(size=(2, h, n+1))
    bias = rng.normal(size=2)
    signs = rng.choice([-1, 1], (h, n+1))
    rawplus = np.exp(bias[0]) + ((z*np.exp(a)*(signs > 0)).sum(2) /
                                        (z*np.exp(b)).sum(2)).sum(1)
    rawminus = np.exp(bias[1]) + ((z*np.exp(a)*(signs < 0)).sum(2) /
                                         (z*np.exp(b)).sum(2)).sum(1)
    aa = torch.tensor(a, dtype=torch.float64, requires_grad=True)
    bb = torch.tensor(b, dtype=torch.float64, requires_grad=True)
    bc = torch.tensor(bias, dtype=torch.float64, requires_grad=True)
    args = (torch.tensor(z.astype(bool)), torch.tensor(signs))
    result = log_difference(aa, bb, bc, *args)
    assert np.max(np.abs(result.detach().numpy()-np.log(rawplus/rawminus))) < 1e-12
    weights = torch.arange(1, len(x)+1, dtype=torch.float64)
    (result*weights).sum().backward()
    maximum_error = 0.
    for parameter in (aa, bb, bc):
        analytic = parameter.grad.detach().numpy().copy()
        for index in np.ndindex(parameter.shape):
            with torch.no_grad():
                parameter[index] += 1e-6
            hi = float((log_difference(aa, bb, bc, *args)*weights).sum())
            with torch.no_grad():
                parameter[index] -= 2e-6
            lo = float((log_difference(aa, bb, bc, *args)*weights).sum())
            with torch.no_grad():
                parameter[index] += 1e-6
            maximum_error = max(maximum_error, abs((hi-lo)/2e-6-analytic[index]))
    assert maximum_error < 1e-7, maximum_error
    return {"direct_log_identity": True, "maximum_gradient_error": maximum_error}


def run(n, h, seed, seconds, out, label_kind):
    start = time.monotonic()
    rng = np.random.default_rng(seed)
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    ynp = rng.choice([-1., 1.], len(x))
    if label_kind == "parity":
        ynp = 1-2*(x.sum(1) % 2)
    y = torch.tensor(ynp, dtype=torch.float64)
    best_errors, best_margin = len(x), -float("inf")
    certificate = None
    events = []
    restart, total_steps = 0, 0
    while time.monotonic()-start < seconds and certificate is None:
        orientation = rng.choice([-1, 1], h)
        active_np = np.concatenate((np.ones((len(x), h, 1), dtype=bool),
            np.where(orientation[None, :, None] > 0, x[:, None], 1-x[:, None]).astype(bool)), axis=2)
        active = torch.tensor(active_np)
        signs_np = rng.choice([-1, 1], (h, n+1))
        signs = torch.tensor(signs_np)
        a = torch.nn.Parameter(torch.tensor(rng.normal(0, 2, (h, n+1)), dtype=torch.float64))
        b = torch.nn.Parameter(torch.tensor(rng.normal(0, 2, (h, n+1)), dtype=torch.float64))
        bias = torch.nn.Parameter(torch.zeros(2, dtype=torch.float64))
        parameters = [a, b, bias]
        adam = torch.optim.Adam(parameters, lr=.03)
        lbfgs = torch.optim.LBFGS(parameters, lr=1., max_iter=30,
                                history_size=30, line_search_fn="strong_wolfe")
        target_margin = .1
        last_log = time.monotonic()
        for step in range(10000):
            if time.monotonic()-start >= seconds:
                break
            def closure(optimizer):
                optimizer.zero_grad()
                difference = log_difference(a, b, bias, active, signs)
                loss = (torch.relu(target_margin-y*difference)/target_margin).square().mean()
                loss.backward()
                return loss
            loss = closure(adam)
            if not torch.isfinite(loss):
                break
            torch.nn.utils.clip_grad_norm_(parameters, 100.)
            adam.step()
            with torch.no_grad():
                # Both are gauge changes: scale numerator and denominator of
                # each head equally; then scale the entire score positively.
                gauge = b[:, :1].clone()
                b.sub_(gauge)
                a.sub_(gauge)
                common = a.mean().clone()
                a.sub_(common)
                bias.sub_(common)
                # Bounds only constrain this finite search, not the model.
                for p in parameters:
                    p.clamp_(-100., 100.)
            if step % 250 == 249:
                lbfgs.step(lambda: closure(lbfgs))
                with torch.no_grad():
                    for p in parameters:
                        p.clamp_(-100., 100.)
            total_steps += 1
            if step % 100 == 99:
                with torch.no_grad():
                    margin = y*log_difference(a, b, bias, active, signs)
                    errors = int((margin <= 0).sum())
                    minimum = float(margin.min())
                if errors < best_errors or minimum > best_margin:
                    np.savez(out/"checkpoint.npz", a=a.detach().numpy(),
                        b=b.detach().numpy(), bias=bias.detach().numpy(),
                        signs=signs_np, orientation=orientation, labels=ynp)
                best_errors, best_margin = min(errors, best_errors), max(minimum, best_margin)
                if time.monotonic()-last_log > 30 or minimum > 1e-10:
                    event = {"restart": restart, "step": step+1,
                             "seconds": time.monotonic()-start,
                             "errors": errors, "minimum_log_margin": minimum,
                             "target_log_margin": target_margin,
                             "loss": float(loss.detach())}
                    events.append(event)
                    print(json.dumps(event), flush=True)
                    last_log = time.monotonic()
                if minimum > 1e-10:
                    cert = export(n, ynp, a.detach().numpy(), b.detach().numpy(),
                                  bias.detach().numpy(), signs_np, orientation)
                    for precision in (160, 512, 2048):
                        checked = exact_check(cert, precision=precision)
                        if checked["certified"]:
                            cert["verification"] = checked
                            certificate = "certificate.json"
                            (out/certificate).write_text(json.dumps(cert)+"\n")
                            break
                    if certificate is not None:
                        break
            if step % 2000 == 1999:
                target_margin *= .1
                lbfgs = torch.optim.LBFGS(parameters, lr=1., max_iter=30,
                    history_size=30, line_search_fn="strong_wolfe")
        restart += 1
    result = {"n": n, "heads": h, "seed": seed, "labels": label_kind,
              "seconds": time.monotonic()-start, "steps": total_steps,
              "best_errors": best_errors, "best_log_margin": best_margin,
              "certificate": certificate, "events": events,
              "failure_is_not_a_lower_bound": True}
    (out/"result.json").write_text(json.dumps(result)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k != "events"}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=8)
    parser.add_argument("--heads", type=int, default=16)
    parser.add_argument("--seed", type=int, default=450001)
    parser.add_argument("--seconds", type=float, default=7200)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--labels", choices=["random", "parity"], default="random")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.check:
        result = smoke_check()
        (args.out/"gradient-check.json").write_text(json.dumps(result)+"\n")
        print(json.dumps(result))
    else:
        run(args.n, args.heads, args.seed, args.seconds, args.out, args.labels)
