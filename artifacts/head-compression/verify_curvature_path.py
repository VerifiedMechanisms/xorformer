#!/usr/bin/env python3
"""Interval audit of an explicit admissible path of affine-fraction scores.

Inputs specify exact rational positive slopes, values, and path velocities.
Each slope evolves by a positive exponential. The path stays admissible
for every real path parameter. This independently evaluates all cube vertices;
it imports no optimization code. Requires python-flint; run large cases via heavy.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
from flint import arb, fmpq, ctx


def number(pair):
    return arb(fmpq(pair[0], pair[1]))


def tables(data, step=None, derivatives=False):
    n = data["n"]
    count = 1 << n
    bias, velocity = number(data["bias"]), number(data["bias_velocity"])
    step = arb(0) if step is None else step
    score = [bias+step*velocity for _ in range(count)]
    first = [velocity for _ in range(count)] if derivatives else None
    second = [arb(0) for _ in range(count)] if derivatives else None
    started = time.monotonic()
    for h, head in enumerate(data["heads"]):
        orientation = head["orientation"]
        assert orientation in (-1, 1)
        slopes = list(map(number, head["slopes"]))
        values = list(map(number, head["values"]))
        dl = list(map(number, head["log_velocity"]))
        dv = list(map(number, head["value_velocity"]))
        assert len(slopes) == len(values) == len(dl) == len(dv) == n
        assert all(bi > 0 for bi in slopes)
        b = [slopes[i]*(step*dl[i]).exp() for i in range(n)]
        v = [values[i]+step*dv[i] for i in range(n)]
        components = [b, [b[i]*v[i] for i in range(n)]]
        if derivatives:
            components += [
                [b[i]*dl[i] for i in range(n)],
                [b[i]*(dv[i]+v[i]*dl[i]) for i in range(n)],
                [b[i]*dl[i]**2 for i in range(n)],
                [b[i]*(2*dv[i]*dl[i]+v[i]*dl[i]**2) for i in range(n)]]
        sums = [sum(c, arb(0)) if orientation < 0 else arb(0)
                for c in components]
        previous = 0
        for address in range(count):
            vertex = address^(address >> 1)
            if address:
                bit = (vertex^previous).bit_length()-1
                sign = 1 if ((vertex >> bit) & 1) else -1
                sign *= orientation
                sums = [s+sign*c[bit] for s, c in zip(sums, components)]
            denominator, numerator = 1+sums[0], sums[1]
            assert denominator > 0
            inverse = 1/denominator
            q = numerator*inverse
            score[vertex] += q
            if derivatives:
                d1, a1, d2, a2 = sums[2:]
                q1 = (a1-q*d1)*inverse
                q2 = (a2-q*d2-2*q1*d1)*inverse
                first[vertex] += q1
                second[vertex] += q2
            previous = vertex
        if (h+1) % 10 == 0:
            print(json.dumps({"phase": "derivatives" if derivatives else "trial",
                              "heads_checked": h+1,
                              "seconds": time.monotonic()-started}), flush=True)
    return score, first, second


def loss(data, score):
    total = arb(0)
    active = 0
    for label, value in zip(data["labels"], score):
        r = 1-label*value
        if r > 0:
            total += r*r
            active += 1
        elif r < 0:
            pass
        else:
            raise ArithmeticError("A hinge kink is not separated by the intervals")
    return total/(2*len(score)), active


def verify(path, out, bits, step_denominator):
    ctx.prec = bits
    raw = path.read_bytes()
    data = json.loads(raw)
    count = 1 << data["n"]
    assert len(data["labels"]) == count
    assert all(y in (-1, 1) for y in data["labels"])
    started = time.monotonic()
    score, first, second = tables(data, derivatives=True)
    base_loss, active = loss(data, score)
    first_loss, second_loss = arb(0), arb(0)
    for y, f, d1, d2 in zip(data["labels"], score, first, second):
        r = 1-y*f
        if r > 0:
            first_loss -= y*r*d1
            second_loss += d1*d1-y*r*d2
        else:
            assert r < 0
    first_loss /= count
    second_loss /= count
    result = dict(input_sha256=hashlib.sha256(raw).hexdigest(),
                  n=data["n"], heads=len(data["heads"]), vertices_checked=count,
                  precision_bits=bits, all_hinge_kinks_separated=True,
                  active_vertices=active, loss_interval=str(base_loss),
                  first_derivative_interval=str(first_loss),
                  second_derivative_interval=str(second_loss),
                  strictly_negative_second_derivative=bool(second_loss < 0),
                  scope="This explicit admissible path only; no universal bound.")
    print(json.dumps(result), flush=True)
    step_sign = -1 if first_loss > 0 else 1
    step = arb(fmpq(step_sign, step_denominator))
    trial, _, _ = tables(data, step=step)
    trial_loss, _ = loss(data, trial)
    difference = trial_loss-base_loss
    result.update(step=[step_sign, step_denominator],
                  trial_loss_interval=str(trial_loss),
                  loss_change_interval=str(difference),
                  strictly_decreases_loss=bool(difference < 0),
                  seconds=time.monotonic()-started)
    out.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result), flush=True)
    assert result["strictly_negative_second_derivative"]
    assert result["strictly_decreases_loss"]


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("path", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--bits", type=int, default=256)
    p.add_argument("--step-denominator", type=int, default=1000000)
    args = p.parse_args()
    verify(args.path, args.out, args.bits, args.step_denominator)
