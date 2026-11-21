#!/usr/bin/env python3
"""Attempt head deletion by monotone single-head linear programs.

Fixing every other head makes a lower bound on the cleared margin linear in
the numerator and denominator coefficients of the remaining head. Successful
final scores are checked using integers. Failure has no lower-bound meaning.
"""
import argparse
import json
import os
from pathlib import Path
import time
for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"
import numpy as np
from scipy.optimize import linprog
from search_sign_scores import exact_check, integer_pair


def unpack(cert):
    n = cert["n"]
    aa, bb, oo = [], [], []
    for h in cert["heads"]:
        a, b = h["numerator"], h["denominator"]
        o = 1 if b[1] > 0 else -1
        maximum = b[0] + sum(v for v in b[1:] if v > 0)
        aa.append([v / maximum for v in a])
        if o > 0:
            bb.append([v / maximum for v in b])
        else:
            bb.append([(b[0] + sum(b[1:])) / maximum] + [-v / maximum for v in b[1:]])
        oo.append(o)
    return np.array(aa), np.array(bb), np.array(oo), cert["bias"][0] / cert["bias"][1]


def pack(n, labels, a, b, o, c):
    heads = []
    for ah, bh, oh in zip(a, b, o):
        d = bh.copy()
        if oh < 0:
            d[0] += d[1:].sum()
            d[1:] *= -1
        ai, bi = integer_pair(ah, d)
        heads.append({"numerator": ai, "denominator": bi})
    return {"n": n, "labels": labels.astype(int).tolist(), "heads": heads,
            "bias": list(float(c).as_integer_ratio()),
            "scope": "This finite truth table only; not a universal upper bound."}


def improve(n, y, a, b, o, c, deadline, rng, max_passes=200):
    x = ((np.arange(1 << n)[:, None] >> np.arange(n)) & 1).astype(float)
    z = np.column_stack((np.ones(len(x)), x))
    tn = np.column_stack((np.ones(len(x)), 1 - x))
    def values():
        denominator = np.column_stack([(z if oh > 0 else tn) @ bh for bh, oh in zip(b, o)])
        return (z @ a.T) / denominator
    v = values()
    s = c + v.sum(axis=1)
    events = []
    for p in range(max_passes):
        before = float(np.min(y * s))
        if before > 1e-6 or time.monotonic() >= deadline:
            break
        for h in rng.permutation(len(a)):
            if time.monotonic() >= deadline:
                break
            old_margin = float(np.min(y * s))
            other = s - v[:, h]
            best = None
            for oh in (o[h], -o[h]):
                t = z if oh > 0 else tn
                # B has maximum one; rho > 0 guarantees at least rho
                # improvement in the true minimum margin.
                matrix = np.column_stack((-y[:, None] * z,
                    -(y * other - old_margin)[:, None] * t, np.ones(len(x))))
                objective = np.zeros(2 * (n + 1) + 1)
                objective[-1] = -1
                equality = np.r_[np.zeros(n + 1), np.ones(n + 1), 0.][None, :]
                eps = max(1e-13, min(1e-6, float(b[h].min()) * .5))
                result = linprog(objective, A_ub=matrix, b_ub=np.zeros(len(x)),
                    A_eq=equality, b_eq=[1.],
                    bounds=[(None, None)] * (n + 1) + [(eps, None)] * (n + 1) + [(None, 1000.)],
                    method="highs", options={"time_limit": max(.1, deadline - time.monotonic())})
                if not result.success:
                    continue
                na, nb = result.x[:n + 1], result.x[n + 1:2 * (n + 1)]
                nv = (z @ na) / (t @ nb)
                ns = other + nv
                margin = float(np.min(y * ns))
                if np.all(nb > 0) and margin > old_margin + 1e-10 and (best is None or margin > best[0]):
                    best = (margin, na, nb, oh, nv, ns)
            if best is not None:
                _, a[h], b[h], o[h], v[:, h], s = best
        margin = float(np.min(y * s))
        events.append({"pass": p, "minimum_margin": margin, "errors": int((y * s <= 0).sum())})
        if margin <= before + 1e-10:
            break
    return a, b, o, c, events


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--certificate", type=Path, required=True)
    p.add_argument("--seconds", type=float, default=1800)
    p.add_argument("--trial-seconds", type=float, default=120)
    p.add_argument("--seed", type=int, default=300)
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    cert = json.loads(args.certificate.read_text())
    if not exact_check(cert)["certified"]:
        raise ValueError("Starting score is not certified")
    n, y = cert["n"], np.array(cert["labels"])
    a, b, o, c = unpack(cert)
    rng = np.random.default_rng(args.seed)
    deadline = time.monotonic() + args.seconds
    k = 0
    while time.monotonic() < deadline and len(a) > 1:
        deleted = k % len(a)
        keep = np.arange(len(a)) != deleted
        na, nb, no, nc, events = improve(n, y, a[keep].copy(), b[keep].copy(), o[keep].copy(), c,
             min(deadline, time.monotonic() + args.trial_seconds), rng)
        candidate = pack(n, y, na, nb, no, nc)
        check = exact_check(candidate)
        success = check["certified"]
        record = {"trial": k, "n": n, "heads": len(na), "deleted": deleted,
                  "certified": success, "events": events,
                  "failure_is_not_a_lower_bound": True}
        if success:
            candidate["verification"] = check
            name = f"n{n}-h{len(na)}-trial{k}.json"
            (args.out / name).write_text(json.dumps(candidate) + "\n")
            record["certificate"] = name
            a, b, o, c = na, nb, no, nc
        with (args.out / "trials.jsonl").open("a") as f:
            f.write(json.dumps(record) + "\n")
        print(json.dumps({key: value for key, value in record.items() if key != "events"}), flush=True)
        k += 1


if __name__ == "__main__":
    main()
