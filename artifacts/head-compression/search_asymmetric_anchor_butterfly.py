#!/usr/bin/env python3
"""Finite sign-only audit of the asymmetric-anchor assignment reader.

For the explicit hierarchical permutation code, search linear coefficients
in sum_h (A[q,h]-G[h,pi(h)])/(D[q]-pole[pi(h)])+bias[q].
The probe and pole choices are fixed in each LP. A successful numerical LP
is only a candidate and requires an exact rational sign audit. Infeasibility
is only numerical evidence for those fixed arguments. Use through heavy.
"""
import argparse
import importlib.util
import itertools
import json
import os
from pathlib import Path
import time

for variable in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[variable] = "1"
import numpy as np
from scipy.optimize import linprog
from scipy.linalg import qr

spec = importlib.util.spec_from_file_location(
    "hierarchy", Path(__file__).with_name("check-hierarchical-cauchy.py"))
hierarchy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(hierarchy)


def state_table(heads):
    descriptors = hierarchy.queries(heads)
    signs = np.array(list(itertools.product((-1, 1), repeat=len(descriptors))), dtype=float)
    permutations = np.array([hierarchy.encode(heads, row, descriptors) for row in signs]) - 1
    return descriptors, signs, permutations


def constraint_matrix(poles, probes, signs, permutations, anchor_probes=None, base_probe=None):
    states, queries = signs.shape
    heads = len(poles)
    variables = queries * heads + heads * heads + queries
    matrix = np.zeros((states * queries, variables))
    if anchor_probes is not None:
        cauchy = 1 / (anchor_probes[:, None] - poles[None, :])
        inverse = np.linalg.inv(cauchy)
        # Shape state, anchor, slot for the anchor right-hand side.
        anchor_kernel = cauchy[:, permutations].transpose(1, 0, 2)
    for q, probe in enumerate(probes):
        rows = np.arange(states) * queries + q
        kernels = 1 / (probe - poles[permutations])
        matrix[rows, q * heads:(q + 1) * heads] = kernels
        residue_kernels = kernels if base_probe is None else (
            kernels - 1 / (base_probe - poles[permutations]))
        if anchor_probes is None:
            for h in range(heads):
                matrix[rows, queries * heads + h * heads + permutations[:, h]] = -residue_kernels[:, h]
        else:
            # c_slot = -sum_anchor Cinv[token_at_slot,anchor]
            #                  * sum_g a[anchor,g] C[anchor,token_at_g].
            height = np.einsum("sh,shi->si", residue_kernels, inverse[permutations])
            matrix[rows, queries * heads:queries * heads + heads * heads] = (
                -height[:, :, None] * anchor_kernel).reshape(states, heads * heads)
        matrix[rows, queries * heads + heads * heads + q] = 1
    matrix *= signs.reshape(-1, 1)
    return matrix


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--heads", type=int, default=8)
    parser.add_argument("--rounds", type=int, default=100)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=240411)
    parser.add_argument("--seconds", type=float, default=1800)
    parser.add_argument("--head-probes", action="store_true",
                        help="Allow a different fixed probe for each query/head pair.")
    parser.add_argument("--solved-anchors", action="store_true",
                        help="Use residues solved at virtual Cauchy anchors, not an edge table.")
    parser.add_argument("--subtract-base", action="store_true",
                        help="Use a column bias canceling the residue readout at probe 1.")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    descriptors, signs, permutations = state_table(args.heads)
    rng = np.random.default_rng(args.seed)
    start = time.monotonic()
    for trial in range(args.rounds):
        if time.monotonic() - start > args.seconds:
            break
        # The first two regimes are deliberately broader than admissible
        # large-column libraries. Later regimes test compact choices.
        compactness = (0.8, 0.5, 0.1, 0.01)[trial % 4]
        poles = np.sort(rng.uniform(0, compactness, args.heads))
        probe_shape = ((len(descriptors), args.heads) if args.head_probes
                       else len(descriptors))
        probes = 1 + rng.uniform(0, compactness, probe_shape)
        anchor_probes = None
        if args.solved_anchors:
            # Virtual equations impose no denominator admissibility condition.
            # Place each anchor near its pole to control inverse conditioning.
            clearance = np.min(np.diff(poles))
            anchor_probes = poles + rng.uniform(0.2, 0.8, args.heads) * clearance
        matrix = constraint_matrix(poles, probes, signs, permutations, anchor_probes,
                                   1 if args.subtract_base else None)
        # Orthonormal columns remove scale and exact gauge degeneracies.
        Q, R, pivots = qr(matrix, mode="economic", pivoting=True)
        diagonal = np.abs(np.diag(R))
        rank = int(np.sum(diagonal > diagonal[0] * 1e-12))
        reduced = Q[:, :rank]
        active = rng.choice(len(reduced), min(400, len(reduced)), replace=False)
        for generation in range(60):
            result = linprog(np.zeros(rank), A_ub=-reduced[active], b_ub=-np.ones(len(active)),
                             bounds=[(None, None)] * rank, method="highs",
                             options={"time_limit": min(30, args.seconds)})
            if not result.success:
                break
            reduced_margins = reduced @ result.x
            violations = np.flatnonzero(reduced_margins < 0.999)
            if not len(violations):
                break
            worst = violations[np.argsort(reduced_margins[violations])[:150]]
            active = np.unique(np.concatenate((active, worst)))
        report = {"trial": trial, "seconds": time.monotonic() - start,
                  "heads": args.heads, "queries": len(descriptors),
                  "head_probes": args.head_probes,
                  "solved_anchors": args.solved_anchors,
                  "subtract_base": args.subtract_base,
                  "states": len(signs), "compactness": compactness,
                  "rank": rank, "generation": generation, "active": len(active),
                  "status": int(result.status), "message": result.message}
        if result.success and np.min(reduced @ result.x) >= 0.999:
            coefficient = np.zeros(matrix.shape[1])
            coefficient[pivots[:rank]] = np.linalg.solve(R[:rank, :rank], result.x)
            margins = matrix @ coefficient
            report["minimum_margin"] = float(np.min(margins))
            np.savez(args.out / f"candidate-{trial}.npz", poles=poles, probes=probes,
                     anchor_probes=anchor_probes,
                     coefficient=coefficient, signs=signs, permutations=permutations)
        print(json.dumps(report), flush=True)
        with (args.out / "search.jsonl").open("a") as stream:
            stream.write(json.dumps(report) + "\n")


if __name__ == "__main__":
    main()
