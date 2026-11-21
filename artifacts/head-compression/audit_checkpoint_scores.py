#!/usr/bin/env python3
"""Recompute saved affine-fraction scores without importing search code.

Extended precision is a numerical diagnostic, not interval or sign
certification. Run large checkpoints with the shared heavy command.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path

import numpy as np


def audit(directory):
    path = directory / "checkpoint.npz"
    raw = path.read_bytes()
    with np.load(io.BytesIO(raw)) as saved:
        labels = saved["labels"].astype(np.longdouble)
        orientation = saved["orientation"].astype(int)
        logs = saved["logs"].astype(np.longdouble)
        coefficient = saved["coefficients"].astype(np.longdouble)
    heads, n = logs.shape
    assert len(labels) == 1 << n
    assert np.all((labels == -1) | (labels == 1))
    assert orientation.shape == (heads,)
    assert np.all((orientation == -1) | (orientation == 1))
    assert coefficient.shape == (1 + heads * n,)
    assert np.all(np.isfinite(logs)) and np.all(np.isfinite(coefficient))
    slopes = np.exp(logs)
    assert np.all(np.isfinite(slopes)) and np.all(slopes > 0)
    numerator_coefficients = coefficient[1:].reshape(heads, n)
    scores = np.empty(len(labels), dtype=np.longdouble)
    for start in range(0, len(labels), 128):
        stop = min(start + 128, len(labels))
        bits = ((np.arange(start, stop)[:, None] >> np.arange(n)) & 1)
        coordinates = np.where(orientation[None, :, None] > 0,
                               bits[:, None], 1 - bits[:, None])
        denominators = 1 + np.sum(coordinates * slopes, axis=2)
        numerators = np.sum(coordinates * numerator_coefficients, axis=2)
        scores[start:stop] = coefficient[0] + np.sum(numerators / denominators, axis=1)
    assert np.all(np.isfinite(scores))
    margins = labels * scores
    residuals = np.maximum(1 - margins, 0)
    loss = np.sum(residuals * residuals) / (2 * len(labels))
    result = {
        "directory": str(directory),
        "checkpoint_sha256": hashlib.sha256(raw).hexdigest(),
        "labels_sha256": hashlib.sha256(labels.astype(np.int8).tobytes()).hexdigest(),
        "n": n,
        "heads": heads,
        "positive_orientation_heads": int(np.count_nonzero(orientation == 1)),
        "vertices": len(labels),
        "longdouble_mantissa_bits": int(np.finfo(np.longdouble).nmant),
        "direct_longdouble_loss": float(loss),
        "errors": int(np.count_nonzero(margins <= 0)),
        "minimum_margin": float(margins.min()),
        "scope": "Numerical extended-precision diagnostic, not interval or sign certification.",
    }
    recorded = directory / "result.json"
    if recorded.exists():
        data = json.loads(recorded.read_text())
        if "final_loss" in data:
            result["reported_final_loss"] = data["final_loss"]
            result["loss_difference"] = float(loss - data["final_loss"])
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directories", nargs="+", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    reports = []
    for directory in args.directories:
        report = audit(directory)
        reports.append(report)
        print(json.dumps(report), flush=True)
    args.out.write_text(json.dumps(reports, indent=2) + "\n")
