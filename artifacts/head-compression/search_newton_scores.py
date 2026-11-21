#!/usr/bin/env python3
"""Tangent least-squares search; only exported integer checks are certificates.

The normal chart eliminates one redundant numerator coordinate per head.
This is a numerical experiment, not a universal construction or a lower bound.
Run through `heavy`.
"""
import argparse
import json
import math
import os
from pathlib import Path
import time

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import numpy as np
import scipy.linalg
from search_sign_scores import exact_check, integer_pair


def export(n, y, u, b, orientation, c):
    heads = []
    for uh, bh, o in zip(u, b, orientation):
        a = np.r_[0., uh] if o > 0 else np.r_[uh.sum(), -uh]
        d = np.r_[1., bh] if o > 0 else np.r_[1. + bh.sum(), -bh]
        ai, bi = integer_pair(a, d)
        heads.append({"numerator": ai, "denominator": bi})
    return {"n": n, "labels": y.astype(int).tolist(), "heads": heads,
            "bias": list(float(c).as_integer_ratio()),
            "scope": "This finite truth table only; not a universal upper bound."}


def trial(n, heads, seed, seconds, outdir, label_kind="random"):
    start = time.monotonic()
    rng = np.random.default_rng(seed)
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    if label_kind == "parity":
        y = 1. - 2. * (x.sum(axis=1) % 2)
    elif label_kind == "bent":
        y = 1. - 2. * ((x[:, :n // 2] * x[:, n // 2:2 * (n // 2)]).sum(axis=1) % 2)
    else:
        y = rng.choice([-1., 1.], len(x))
    orientation = rng.choice([-1, 1], heads)
    t = np.where(orientation[None, :, None] > 0, x[:, None, :], 1 - x[:, None, :])
    u = rng.normal(0, .1 / math.sqrt(heads), (heads, n))
    logs = rng.normal(0, 2, (heads, n))
    c = y.mean()
    best_errors, best_loss = len(x), math.inf
    best_state = None
    steps = 0
    damping = 1e-4
    events = []

    def evaluate(uu, ll, cc, jacobian=False):
        b = np.exp(np.clip(ll, -30, 30))
        d = 1 + np.einsum("xhi,hi->xh", t, b)
        v = np.einsum("xhi,hi->xh", t, uu)
        s = cc + (v / d).sum(axis=1)
        if not jacobian:
            return s
        ju = t / d[:, :, None]
        jl = -v[:, :, None] * ju * b[None, :, :] / d[:, :, None]
        j = np.column_stack((np.ones(len(x)), ju.reshape(len(x), -1), jl.reshape(len(x), -1)))
        return s, j

    while time.monotonic() - start < seconds:
        s, j = evaluate(u, logs, c, True)
        margins = y * s
        r = np.maximum(1 - margins, 0)
        loss = np.mean(r * r)
        errors = int((margins <= 0).sum())
        best_errors = min(best_errors, errors)
        if loss < best_loss:
            best_loss = loss
            best_state = (u.copy(), logs.copy(), c)
        if margins.min() > 1e-7:
            cert = export(n, y, u, np.exp(np.clip(logs, -30, 30)), orientation, c)
            check = exact_check(cert)
            if check["certified"]:
                cert["verification"] = check
                name = f"{label_kind}-n{n}-h{heads}-seed{seed}.json"
                (outdir / name).write_text(json.dumps(cert) + "\n")
                return {"n": n, "heads": heads, "seed": seed, "label_kind": label_kind,
                        "steps": steps, "seconds": time.monotonic() - start,
                        "best_errors": best_errors, "certificate": name}
        active = r > 0
        ja = y[active, None] * j[active]
        ra = r[active]
        column_scale = np.maximum(np.linalg.norm(ja, axis=0), 1e-30)
        ja = ja / column_scale
        # Damped minimum-norm tangent correction, solved in the smaller space.
        if ja.shape[0] < ja.shape[1]:
            gram = ja @ ja.T
            ridge = damping * max(np.trace(gram) / len(gram), 1e-20)
            gram.flat[::len(gram) + 1] += ridge
            delta = ja.T @ scipy.linalg.solve(gram, ra, assume_a="pos")
        else:
            gram = ja.T @ ja
            ridge = damping * max(np.trace(gram) / len(gram), 1e-20)
            gram.flat[::len(gram) + 1] += ridge
            delta = scipy.linalg.solve(gram, ja.T @ ra, assume_a="pos")
        delta = delta / column_scale
        dc = delta[0]
        du = delta[1:1 + heads * n].reshape(heads, n)
        dl = delta[1 + heads * n:].reshape(heads, n)
        alpha = min(1., 2 / max(np.abs(dl).max(), 1e-30))
        accepted = False
        for _ in range(18):
            nu, nl, nc = u + alpha * du, np.clip(logs + alpha * dl, -30, 30), c + alpha * dc
            ns = evaluate(nu, nl, nc)
            new_loss = np.mean(np.maximum(1 - y * ns, 0) ** 2)
            if new_loss < loss - max(1e-14, loss * 1e-10):
                u, logs, c = nu, nl, nc
                accepted = True
                break
            alpha *= .5
        if accepted:
            damping = max(damping * .7, 1e-8)
        else:
            damping = min(damping * 10, 1e2)
            if damping >= 1e2:
                u, logs, c = best_state
                u, logs = u.copy(), logs + rng.normal(0, .15, logs.shape)
                damping = 1e-4
        steps += 1
        if steps % 100 == 0:
            events.append({"step": steps, "loss": loss, "errors": errors,
                           "damping": damping, "elapsed": time.monotonic() - start})
    np.savez(outdir / f"checkpoint-{label_kind}-n{n}-h{heads}-seed{seed}.npz",
             numerator=best_state[0], logs=best_state[1], bias=best_state[2],
             orientation=orientation, labels=y)
    return {"n": n, "heads": heads, "seed": seed, "label_kind": label_kind,
            "steps": steps, "seconds": time.monotonic() - start,
            "best_errors": best_errors, "best_loss": best_loss, "certificate": None,
            "failure_is_not_a_lower_bound": True, "events": events}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--seconds", type=float, default=600)
    p.add_argument("--trial-seconds", type=float, default=120)
    p.add_argument("--dimensions", type=int, nargs="+", default=[9, 10, 11])
    p.add_argument("--constants", type=float, nargs="+", default=[2, 3, 4])
    p.add_argument("--seed", type=int, default=40000)
    p.add_argument("--labels", choices=["random", "parity", "bent"], default="random")
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    k = 0
    while time.monotonic() - start < args.seconds:
        n = args.dimensions[k % len(args.dimensions)]
        constant = args.constants[(k // len(args.dimensions)) % len(args.constants)]
        h = max(n, math.ceil(constant * (1 << n) / n**2))
        result = trial(n, h, args.seed + k, min(args.trial_seconds, args.seconds - (time.monotonic() - start)),
                       args.out, args.labels)
        with (args.out / "trials.jsonl").open("a") as f:
            f.write(json.dumps(result) + "\n")
        print(json.dumps({a: b for a, b in result.items() if a != "events"}), flush=True)
        k += 1


if __name__ == "__main__":
    main()
