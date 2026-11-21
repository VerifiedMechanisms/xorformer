#!/usr/bin/env python3
"""Audit the base score of an exact rational path file using Arb intervals.

This reports errors as well as successes. It does not assert a universal
construction or interpret unsuccessful checkpoints as lower bounds.
"""
import argparse
import hashlib
import json
from pathlib import Path
from flint import ctx
from verify_curvature_path import tables, loss


def audit(path, bits):
    ctx.prec = bits
    raw = path.read_bytes()
    data = json.loads(raw)
    assert len(data["labels"]) == 1 << data["n"]
    assert all(y in (-1, 1) for y in data["labels"])
    score, _, _ = tables(data)
    value, active = loss(data, score)
    margins = [y*s for y, s in zip(data["labels"], score)]
    positive = sum(bool(m > 0) for m in margins)
    negative = sum(bool(m < 0) for m in margins)
    return dict(input_sha256=hashlib.sha256(raw).hexdigest(),
                n=data["n"], heads=len(data["heads"]),
                precision_bits=bits, vertices_checked=len(margins),
                positive_margins_certified=positive,
                negative_margins_certified=negative,
                unseparated_margins=len(margins)-positive-negative,
                active_vertices=active,
                squared_hinge_loss_interval=str(value),
                scope="This exact base score only; no universal bound.")


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("path", type=Path)
    p.add_argument("--bits", type=int, default=256)
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args()
    result = audit(args.path, args.bits)
    args.out.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result), flush=True)
