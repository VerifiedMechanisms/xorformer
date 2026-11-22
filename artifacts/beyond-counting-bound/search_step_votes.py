"""Search finite sums of coordinate threshold votes as reciprocal limits.

Each successful finite configuration is converted to positive rational poles
and witnesses and verified exactly. An incomplete search proves no upper bound.
"""
import argparse
import itertools
import json
from pathlib import Path
import time

import numpy as np

from evolve_separable_mobius import verify


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--heads', type=int, default=3)
    ap.add_argument('--queries', type=int, default=7)
    ap.add_argument('--seconds', type=float, default=3600)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seed', type=int, default=103781)
    args = ap.parse_args()
    h, m = args.heads, args.queries
    points = np.array(list(itertools.product(range(m+1),repeat=h)),dtype=np.int16)
    small_cube = np.array(list(itertools.product([0,1],repeat=h)),dtype=np.int16)
    rules = {}
    for w in itertools.product(range(-2,3),repeat=h):
        values = small_cube@np.array(w)
        for c2 in range(2*int(values.min())-1,2*int(values.max())+2,2):
            code = sum(int(v*2 > c2) << j for j,v in enumerate(values))
            rules.setdefault(code,(w,c2))
    gate_w = np.array([w for w,c in rules.values()],dtype=np.int16)
    gate_c = np.array([c for w,c in rules.values()],dtype=np.int16)
    rng = np.random.default_rng(args.seed)
    threshold = rng.integers(1,m+1,size=(m,h))
    gates = rng.integers(len(rules),size=m)
    bits = 1 << np.arange(m,dtype=np.uint64)

    def row(t,g):
        return 2*((points < t)@gate_w[g]) > gate_c[g]

    masks = sum(row(t,g).astype(np.uint64)*bit for t,g,bit in zip(threshold,gates,bits))
    count = len(np.unique(masks))
    best_count = -1
    best = None
    started = time.monotonic()
    step = 0
    while time.monotonic()-started < args.seconds:
        if count > best_count:
            unique,indices = np.unique(masks,return_index=True)
            base = 64*h+1
            # The exponent gap is at least one. Each sigmoid differs from
            # its step value by at most 1/base, hence score error <=2*h/base.
            poles = [[base**(2*int(k)) for k in t] for t in threshold]
            record = dict(poles=poles,
                          residuals=[[int(w)*p for w,p in zip(gate_w[g],pp)]
                                     for g,pp in zip(gates,poles)],
                          thresholds=[str(int(gate_c[g]))+'/2' for g in gates],
                          witnesses={str(int(mask)):[base**(2*int(k)+1) for k in points[i]]
                                     for mask,i in zip(unique,indices)},
                          patterns=count,total_patterns=2**m,steps=step,
                          step_thresholds=threshold.tolist(),
                          step_weights=gate_w[gates].tolist(),
                          step_twice_biases=gate_c[gates].tolist(),
                          base=base,status='FINITE_WITNESSES_ONLY',
                          elapsed_seconds=time.monotonic()-started)
            verify(record)
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps(record,indent=2)+'\n')
            best_count = count
            best = (threshold.copy(),gates.copy())
            print(json.dumps({k:record[k] for k in ['patterns','total_patterns','steps',
                             'elapsed_seconds']}),flush=True)
            if count == 2**m:
                break
        q = int(rng.integers(m))
        t = threshold[q].copy()
        g = gates[q]
        if rng.random() < .65:
            t[rng.integers(h)] = rng.integers(1,m+1)
        else:
            g = rng.integers(len(rules))
        candidate = (masks & ~bits[q]) | row(t,g).astype(np.uint64)*bits[q]
        new_count = len(np.unique(candidate))
        temperature = .1 if step % 5000 < 4500 else 1.0
        if new_count >= count or rng.random() < np.exp((new_count-count)/temperature):
            threshold[q],gates[q] = t,g
            masks,count = candidate,new_count
        step += 1
        if step % 10000 == 0 and count < best_count:
            threshold,gates = [a.copy() for a in best]
            masks = sum(row(t,g).astype(np.uint64)*bit for t,g,bit in zip(threshold,gates,bits))
            count = len(np.unique(masks))
    print(json.dumps(dict(finished=True,best=best_count,steps=step,
                          elapsed_seconds=time.monotonic()-started,
                          failure_status='UNKNOWN')),flush=True)


if __name__ == '__main__':
    main()
