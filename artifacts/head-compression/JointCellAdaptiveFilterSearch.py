#!/usr/bin/env python3
"""Exploratory adaptive-weight filtered-kernel matrix search.

This is a floating-point screen, not a proof or impossibility certificate.
Every bit and column slope is positive and their total is less than 1/2.
The row denominator has base 1 + sum(weights), so its full-cube gap is
at least 1/2, independently of the positive selected-coordinate weights.
Run nontrivial searches through `heavy` on the shared machine.
"""
import argparse
import json
import math
import numpy as np
import torch


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bits", type=int, default=8)
    ap.add_argument("--columns", type=int, default=8)
    ap.add_argument("--order", type=int, default=8)
    ap.add_argument("--banks", type=int, default=2)
    ap.add_argument("--starts", type=int, default=8)
    ap.add_argument("--steps", type=int, default=1500)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--nodes", type=int, default=64)
    ap.add_argument("--output")
    args = ap.parse_args()
    torch.set_num_threads(1)
    torch.set_default_dtype(torch.float64)
    rng = np.random.default_rng(args.seed)
    target = torch.tensor(rng.choice([-1., 1.], (args.bits, args.columns)))
    nodes, quadrature = np.polynomial.laguerre.laggauss(args.nodes)
    nodes = torch.tensor(nodes)
    log_quadrature = torch.tensor(np.log(quadrature))
    delta = 1 / (2 * (args.bits + args.columns))

    def kernel_log(weights, gap):
        t = nodes[None, None, None, :] / gap[..., None]
        z = weights[:, None, None, :, None] * t[..., None, :]
        log_density = torch.log(-torch.expm1(-z)).sum(-2)
        return torch.logsumexp(log_density + log_quadrature, -1) - torch.log(gap)

    best = None
    for start in range(args.starts):
        torch.manual_seed(args.seed * 1000 + start)
        log_weights = torch.nn.Parameter(torch.randn(args.banks, args.order) * 2)
        bit_raw = torch.nn.Parameter(torch.randn(args.banks, args.bits))
        column_raw = torch.nn.Parameter(torch.randn(args.banks, args.columns))
        coefficient = torch.nn.Parameter(torch.randn(args.banks, args.bits))
        bias = torch.nn.Parameter(torch.zeros(args.bits))
        parameters = [log_weights, bit_raw, column_raw, coefficient, bias]

        def scores():
            weights = torch.exp(log_weights.clamp(-12, 12))
            bit = delta * torch.sigmoid(bit_raw)
            column = delta * torch.sigmoid(column_raw)
            gap = 1 - bit[:, :, None] - column[:, None, :]
            base = 1 - bit[:, :, None]
            feature = torch.expm1(kernel_log(weights, gap) - kernel_log(weights, base)) / delta
            return (coefficient[:, :, None] * feature).sum(0) + bias[:, None]

        optimizer = torch.optim.Adam(parameters, lr=0.04)
        for step in range(args.steps):
            optimizer.zero_grad()
            score = scores()
            loss = torch.nn.functional.softplus(-target * score).mean()
            loss.backward()
            optimizer.step()
        optimizer = torch.optim.LBFGS(parameters, max_iter=500, line_search_fn="strong_wolfe",
                                      tolerance_grad=1e-10, tolerance_change=1e-13)

        def closure():
            optimizer.zero_grad()
            loss = torch.nn.functional.softplus(-target * scores()).mean()
            loss.backward()
            return loss

        optimizer.step(closure)
        with torch.no_grad():
            signed = target * scores()
            result = {"start": start, "minimum_margin": signed.min().item(),
                      "correct": int((signed > 0).sum()), "total": target.numel(),
                      "loss": torch.nn.functional.softplus(-signed).mean().item(),
                      "log_weights": log_weights.tolist(), "bit_raw": bit_raw.tolist(),
                      "column_raw": column_raw.tolist(), "coefficient": coefficient.tolist(),
                      "bias": bias.tolist()}
        print(json.dumps({k: result[k] for k in ["start", "minimum_margin", "correct", "total", "loss"]}), flush=True)
        if best is None or result["loss"] < best["loss"]:
            best = result
        if result["minimum_margin"] > 1:
            break
    record = {"status": "floating-point exploratory search only", "arguments": vars(args),
              "target": target.tolist(), "best": best}
    if args.output:
        with open(args.output, "w") as f:
            json.dump(record, f, indent=2)


if __name__ == "__main__":
    main()
