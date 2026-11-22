"""Longer full-cube searches, with strict separation from lower-bound claims.

Every unsuccessful trial is UNKNOWN. A successful floating-point fit is saved
only after the exact rational certificate builder accepts it; the independent
verifier must still be run on every saved certificate.
"""
import argparse
import json
from pathlib import Path
import time

from search_projected_hinge import fit, gradient_check


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=14400)
    parser.add_argument('--trial-seconds', type=float, default=1200)
    parser.add_argument('--iterations', type=int, default=3000)
    parser.add_argument('--restarts', type=int, default=2)
    parser.add_argument('--cases', type=str, default='11:17,34,51,68;12:29,57,86,114;13:49,97,146,194')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    print(json.dumps({'event': 'gradient_check', 'error': gradient_check()}), flush=True)
    deadline = time.monotonic() + args.seconds
    cases = []
    for item in args.cases.split(';'):
        dimension, widths = item.split(':')
        cases.append((int(dimension), [int(w) for w in widths.split(',')]))
    with (args.output / 'larger-table-results.jsonl').open('a', buffering=1) as log:
        for n, widths in cases:
            for heads in widths:
                for restart in range(args.restarts):
                    if time.monotonic() >= deadline:
                        return
                    trial_deadline = min(deadline, time.monotonic() + args.trial_seconds)
                    print(json.dumps({'event': 'trial_start', 'n': n, 'heads': heads,
                                      'restart': restart}), flush=True)
                    record, certificate = fit(n, heads, restart, args.iterations,
                                              trial_deadline)
                    if certificate:
                        name = f'n{n}-h{heads}-larger-table-r{restart}.json'
                        (args.output / name).write_text(json.dumps(certificate) + '\n')
                        record['certificate'] = name
                    line = json.dumps(record)
                    log.write(line + '\n')
                    print(line, flush=True)
                    if certificate:
                        break


if __name__ == '__main__':
    main()
