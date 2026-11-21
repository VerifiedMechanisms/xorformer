#!/usr/bin/env python3
"""Run distinct exact dominant-power feasibility searches. Use heavy.

Timeouts and UNSAT are recorded only for the specified restricted ansatz.
Each SAT result passes the ordinary rational certificate checker in run().
"""
import argparse
from pathlib import Path
import time
from search_tropical_scores import run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=28800)
    parser.add_argument("--trial-seconds", type=float, default=600)
    parser.add_argument("--mixed-orientations", action="store_true")
    args = parser.parse_args()
    deadline = time.monotonic()+args.seconds
    cases = [(3, 3, "parity"), (4, 4, "parity"), (4, 5, "parity"),
             (5, 6, "random"), (6, 8, "random"), (6, 12, "random")]
    if args.mixed_orientations:
        cases = [(5, 3, "random"), (5, 4, "random"), (6, 5, "random"),
                 (6, 6, "random"), (7, 8, "random"), (7, 11, "random")]
    trial = 0
    while time.monotonic() < deadline:
        n, heads, kind = cases[trial % len(cases)]
        bound = [16, 64, 0][(trial // len(cases)) % 3]
        seed = 170000+trial
        out = args.out/f"{kind}-n{n}-h{heads}-bound{bound}-seed{seed}"
        out.mkdir(parents=True, exist_ok=True)
        run(n, heads, seed, min(args.trial_seconds, deadline-time.monotonic()),
            out, kind, bound, mixed_orientations=args.mixed_orientations)
        trial += 1


if __name__ == "__main__":
    main()
