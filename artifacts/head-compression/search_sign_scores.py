#!/usr/bin/env python3
"""Heuristic search for admissible scores, with independent integer verification.

Success certifies only the specified truth table. Failure is not a lower bound.
Run substantial searches through `heavy`; this program uses one CPU thread.
"""

import argparse
import json
import math
import os
from pathlib import Path
import time

os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import numpy as np
import torch


def exact_check(certificate, precision=160):
    """Enclose the whole score using integer division, without float arithmetic."""
    n = certificate["n"]
    signs = certificate["labels"]
    heads = certificate["heads"]
    scale = 1 << precision
    c_num, c_den = certificate["bias"]
    bias_lo = (scale * c_num) // c_den
    minimum_margin = None
    for x in range(1 << n):
        lo = bias_lo
        for head in heads:
            a, b = head["numerator"], head["denominator"]
            av = a[0] + sum(a[i + 1] for i in range(n) if (x >> i) & 1)
            bv = b[0] + sum(b[i + 1] for i in range(n) if (x >> i) & 1)
            if bv <= 0:
                return {"certified": False, "reason": "nonpositive denominator", "x": x}
            lo += (scale * av) // bv
        # Each floor loses less than one; an extra one accounts for the bias.
        hi = lo + len(heads) + 1
        margin = lo if signs[x] == 1 else -hi
        if margin <= 0:
            return {"certified": False, "reason": "sign interval crosses zero", "x": x}
        minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
    for head in heads:
        slopes = head["denominator"][1:]
        if not (all(v > 0 for v in slopes) or all(v < 0 for v in slopes)):
            return {"certified": False, "reason": "denominator orientation"}
    return {"certified": True, "margin_numerator": minimum_margin,
            "margin_denominator": scale, "vertices_checked": 1 << n}


def integer_pair(a, b):
    pairs = [float(v).as_integer_ratio() for v in list(a) + list(b)]
    denominator = max(q for _, q in pairs)  # All denominators are powers of two.
    values = [p * (denominator // q) for p, q in pairs]
    split = len(a)
    return values[:split], values[split:]


def export_certificate(n, labels, numerator, denominator, orientation, bias):
    heads = []
    for a, b, o in zip(numerator, denominator, orientation):
        b = b.copy()
        if o < 0:
            b[0] += b[1:].sum()
            b[1:] *= -1
        ai, bi = integer_pair(a, b)
        heads.append({"numerator": ai, "denominator": bi})
    return {"n": n, "labels": labels.astype(int).tolist(), "heads": heads,
            "bias": list(float(bias).as_integer_ratio()),
            "scope": "This finite truth table only; not a universal upper bound."}


def run_trial(n, heads, seed, seconds, outdir, method="adam"):
    started = time.monotonic()
    rng = np.random.default_rng(seed)
    torch.manual_seed(seed)
    labels = rng.choice([-1., 1.], 1 << n)
    x_np = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    x = torch.tensor(x_np, dtype=torch.float64)
    z = torch.cat((torch.ones((len(x), 1), dtype=x.dtype), x), dim=1)
    y = torch.tensor(labels, dtype=x.dtype)
    orientation_np = rng.choice([-1, 1], heads)
    orientation = torch.tensor(orientation_np, dtype=x.dtype)
    logits = torch.nn.Parameter(torch.tensor(rng.normal(0, 2, (heads, n + 1)), dtype=x.dtype))
    numerator = torch.nn.Parameter(torch.tensor(rng.normal(0, 0.02 / math.sqrt(heads), (heads, n + 1)), dtype=x.dtype))
    bias = torch.nn.Parameter(torch.tensor(float(labels.mean()), dtype=x.dtype))

    def score():
        b = torch.softmax(logits, dim=1)
        const = b[:, 0] + torch.where(orientation < 0, b[:, 1:].sum(dim=1), 0)
        denom = const + x @ (b[:, 1:] * orientation[:, None]).T
        return bias + ((z @ numerator.T) / denom).sum(dim=1)

    parameters = [logits, numerator, bias]
    optimizer = torch.optim.Adam(parameters, lr=0.025)
    best = len(x)
    best_margin = float("-inf")
    iterations = 0
    loss_value = float("inf")
    certificate_path = None
    while time.monotonic() - started < seconds:
        optimizer.zero_grad()
        s = score()
        # Squared hinge has an actual zero at a finite strictly correct score.
        margins = y * s
        loss = torch.relu(1 - margins).square().mean()
        if not torch.isfinite(loss):
            break
        loss.backward()
        torch.nn.utils.clip_grad_norm_(parameters, 100)
        optimizer.step()
        iterations += 1
        if iterations % 100 == 0:
            with torch.no_grad():
                margins = y * score()
                errors = int((margins <= 0).sum())
                best = min(best, errors)
                best_margin = max(best_margin, float(margins.min()))
                loss_value = float(loss)
                if float(margins.min()) > 1e-7:
                    cert = export_certificate(n, labels, numerator.numpy(force=True),
                                              torch.softmax(logits, dim=1).numpy(force=True),
                                              orientation_np, bias.item())
                    check = exact_check(cert)
                    if check["certified"]:
                        cert["verification"] = check
                        certificate_path = f"n{n}-h{heads}-seed{seed}.json"
                        (outdir / certificate_path).write_text(json.dumps(cert) + "\n")
                        break
            # Periodically refine with a full deterministic quasi-Newton step.
            if method == "hybrid" and iterations % 1000 == 0:
                lbfgs = torch.optim.LBFGS(parameters, max_iter=20, line_search_fn="strong_wolfe")

                def closure():
                    lbfgs.zero_grad()
                    current = torch.relu(1 - y * score()).square().mean()
                    current.backward()
                    return current

                lbfgs.step(closure)
    return {"n": n, "heads": heads, "seed": seed, "method": method,
            "seconds": round(time.monotonic() - started, 3), "iterations": iterations,
            "best_errors": best, "best_minimum_margin": best_margin,
            "final_loss": loss_value, "certificate": certificate_path,
            "failure_is_not_a_lower_bound": True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=300)
    parser.add_argument("--trial-seconds", type=float, default=30)
    parser.add_argument("--dimensions", type=int, nargs="+", default=[5, 6, 7, 8])
    parser.add_argument("--constant", type=float, default=4)
    parser.add_argument("--seed", type=int, default=1000)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--method", choices=["adam", "hybrid"], default="hybrid")
    parser.add_argument("--verify", type=Path)
    args = parser.parse_args()
    if args.verify:
        print(json.dumps(exact_check(json.loads(args.verify.read_text()))))
        return
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    args.out.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    trial = 0
    while time.monotonic() - started < args.seconds:
        n = args.dimensions[trial % len(args.dimensions)]
        heads = max(n, math.ceil(args.constant * (1 << n) / n**2))
        remaining = args.seconds - (time.monotonic() - started)
        result = run_trial(n, heads, args.seed + trial, min(args.trial_seconds, remaining),
                           args.out, args.method)
        with (args.out / "trials.jsonl").open("a") as stream:
            stream.write(json.dumps(result) + "\n")
        print(json.dumps(result), flush=True)
        trial += 1


if __name__ == "__main__":
    main()
