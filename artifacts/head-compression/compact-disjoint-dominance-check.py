#!/usr/bin/env python3
"""Exact identity checks for compact-disjoint-dominance.tex.

The unrestricted lower bound is the written rank proof, not a finite test.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


def prod(xs):
    out = F(1)
    for x in xs:
        out *= x
    return out


def main():
    here = Path(__file__).resolve().parent
    pool = json.loads((here / "rectangular-cauchy-eight-pole-pool.json").read_text())
    poles = list(map(F, pool["p"]))
    times = list(map(F, pool["t"]))
    weights = list(map(F, pool["v"]))
    checks = 0
    for a, b, c, d in product((-1, 1), repeat=4):
        tau = (a, b, c, d, -c, c, -a, a)
        wanted = (d, -a, b, c)
        for t, sign in zip(times, wanted):
            score = sum(v * x / (t - p) for v, x, p in zip(weights, tau, poles))
            assert sign * score > 0
            checks += 1

    # Polynomial padding, with repeated poles included.
    pad_checks = 0
    for ps in ((F(1, 20),), (F(1, 20), F(1, 20)),
               (F(1, 20), F(1, 10), F(3, 20))):
        cs = [F((-1) ** h * (h + 1)) for h in range(len(ps))]
        for L in range(len(ps), 6):
            for t in (F(1), F(3, 2), F(2)):
                Q = t ** (L - len(ps)) * prod(t - p for p in ps)
                score = sum(c / (t - p) for c, p in zip(cs, ps))
                cleared = t ** (L - len(ps)) * sum(
                    cs[h] * prod(t - ps[k] for k in range(len(ps)) if k != h)
                    for h in range(len(ps))
                )
                assert Q * score == cleared
                assert t ** L * F(17, 20) ** L <= Q <= t ** L
                pad_checks += 1

    # Two-pole noncompact filters, with exact strict diagonal dominance.
    noncompact_checks = 0
    for q in (1, 2, 4, 8, 16):
        aa = [F(32 ** j) for j in range(q)]
        for i, t in enumerate(aa):
            row = [a * t / ((t + a) * (t + 2 * a)) for a in aa]
            assert row[i] == F(1, 6)
            assert row[i] > sum(row[j] for j in range(q) if j != i)
            for a, value in zip(aa, row):
                assert value == -a / (t + a) + 2 * a / (t + 2 * a)
            noncompact_checks += 1
    # The gap chart reverses both lists while preserving the obstruction.
    assert F(31, 33)**2 > F(1, 2)
    for scale in (32, 1024, 32768):
        p0, p1, t0, t1 = map(F, (-scale, -1, 1, scale))
        cross = (p1-p0)*(t1-t0)/((t0-p0)*(t1-p1))
        pp = sorted((1/p0, 1/p1)); tt = sorted((1/t0, 1/t1))
        transformed = ((pp[1]-pp[0])*(tt[1]-tt[0])
                       / ((tt[0]-pp[0])*(tt[1]-pp[1])))
        assert transformed == cross >= F(31, 33)**2
    print(f"PASS: {checks} grouped strict signs, {pad_checks} padding identities, "
          f"{noncompact_checks} noncompact dominance rows, 3 projective obstructions")


if __name__ == "__main__":
    main()
