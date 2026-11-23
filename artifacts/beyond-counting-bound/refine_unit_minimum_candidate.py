"""Refine a numerical active set in natural affine-denominator coordinates.

This produces rational approximations for a separate exact contraction audit.
High precision arithmetic in this file is NOT itself a proof of a root.
"""
import argparse
import json
import time
from pathlib import Path

import mpmath as mp


def evaluate(z, bits, n, h):
    values = mp.matrix(len(bits), 1)
    jac = mp.matrix(len(bits), 2*n*h)
    for r, x in enumerate(bits):
        for head in range(h):
            a = sum(z[i*h+head] for i in x)
            b = 1 + sum(z[n*h+i*h+head] for i in x)
            values[r] += a/b
            for i in x:
                jac[r, i*h+head] = 1/b
                jac[r, n*h+i*h+head] = -a/b**2
    return values, jac


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('candidate', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('--digits', type=int, default=100)
    ap.add_argument('--round-digits', type=int, default=70)
    args = ap.parse_args()
    mp.mp.dps = args.digits
    d = json.loads(args.candidate.read_text())
    n, h = d['n'], d['heads']
    q = n*h
    z = mp.matrix([mp.mpf(str(v)) for v in d['theta']])
    for head in range(h):
        p = [mp.exp(z[q+i*h+head]) for i in range(n)]
        total = 1 + sum(p)
        for i in range(n):
            z[q+i*h+head] = p[i] if d['orientation'][head] > 0 else -p[i]/total
    active = d['active_vertices']
    labels = [int(d['labels'][v]) for v in active]
    bits = [[i for i in range(n) if (v >> i) & 1] for v in active]
    gamma = mp.mpf(str(d['gamma']))
    target = mp.matrix([0 if y > 0 else -gamma for y in labels])
    start = time.monotonic()
    for iteration in range(8):
        values, jac = evaluate(z, bits, n, h)
        residual = values-target
        error = max(abs(v) for v in residual)
        print(json.dumps(dict(iteration=iteration, residual=str(error),
                              elapsed=time.monotonic()-start)), flush=True)
        if error < mp.mpf(10)**(-args.digits+15):
            break
        z -= mp.lu_solve(jac, residual)
    values, jac = evaluate(z, bits, n, h)
    inverse = jac**-1
    gradient = mp.matrix([z[i] if i < q else 0 for i in range(2*q)])
    unsigned_dual = inverse.T*gradient
    dual = [unsigned_dual[i]*labels[i] for i in range(2*q)]
    scale = 10**args.round_digits
    integer = lambda v: str(int(mp.nint(v*scale)))
    result = dict(status='RATIONAL_APPROXIMATIONS_ONLY_NOT_A_CERTIFICATE',
                  source=args.candidate.name, n=n, heads=h,
                  denominator=str(scale), gamma=str(d['gamma']),
                  center=[integer(v) for v in z],
                  inverse=[[integer(inverse[i,j]) for j in range(2*q)] for i in range(2*q)],
                  dual=[integer(v) for v in dual],
                  active_vertices=active, active_labels=labels,
                  orientation=d['orientation'],
                  diagnostics=dict(root_residual=str(max(abs(v) for v in values-target)),
                                   minimum_multiplier=str(min(dual)),
                                   inverse_max_row_sum=str(max(sum(abs(inverse[i,j]) for j in range(2*q))
                                                               for i in range(2*q))),
                                   elapsed_seconds=time.monotonic()-start),
                  main_target_proved=False)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result['diagnostics']), flush=True)


if __name__ == '__main__':
    main()
