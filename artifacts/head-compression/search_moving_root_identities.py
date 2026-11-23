#!/usr/bin/env python3
"""Search Boolean multiset identities with an input-dependent root set.

The minimum root is required to be nonaffine on one square. The matching
graph must be connected, excluding identities assembled from independent
fixed-root blocks. All SAT identities and any tangent sign witnesses are
checked exactly. Rank computations use rational arithmetic. This does not
prove the universal head bound. The subsequent analytical obstruction in
laplace-sign-obstruction.tex rules out universality of ideal first
variations at the requested asymptotic budget. Retained as a diagnostic
of finite identities, not as an open universal construction. Run through
heavy.
"""
import argparse
from collections import deque
from fractions import Fraction
import itertools
import json
from pathlib import Path
import random
import time

from flint import fmpq_mat
import z3


def affine(row, bits):
    return row[0] + sum(a*b for a, b in zip(row[1:], bits))


def minimum(values):
    result = values[0]
    for value in values[1:]:
        result = z3.If(result <= value, result, value)
    return result


def verify_identity(u, v):
    m, n = len(u), len(u[0])-1
    assert len(v) == m and all(len(r) == n+1 for r in u+v)
    adjacency = [set() for _ in range(2*m)]
    minima = {}
    for bits in itertools.product((0, 1), repeat=n):
        ur, vr = [affine(r, bits) for r in u], [affine(r, bits) for r in v]
        assert len(set(ur)) == m and sorted(ur) == sorted(vr)
        minima[bits] = min(ur)
        for h, value in enumerate(ur):
            k = vr.index(value)
            adjacency[h].add(m+k)
            adjacency[m+k].add(h)
    seen, queue = {0}, deque([0])
    while queue:
        for k in adjacency[queue.popleft()]:
            if k not in seen:
                seen.add(k)
                queue.append(k)
    assert len(seen) == 2*m
    square = [tuple([a, b]+[0]*(n-2)) for a, b in ((0,0),(1,0),(0,1),(1,1))]
    defect = minima[square[0]]-minima[square[1]]-minima[square[2]]+minima[square[3]]
    assert defect != 0
    return {'vertices_checked': 1 << n, 'distinct_roots_at_every_vertex': True,
            'matching_graph_connected': True, 'minimum_root_square_defect': defect}


def tangent_rows(u, v):
    m, n = len(u), len(u[0])-1
    width = 2*m*(n+1)
    constraints, output = [], []
    for bits in itertools.product((0, 1), repeat=n):
        z = [1]+list(bits)
        ur, vr = [affine(r, bits) for r in u], [affine(r, bits) for r in v]
        rows = []
        for h, value in enumerate(ur):
            residue = 1
            for other, other_value in enumerate(ur):
                if other != h:
                    residue *= other_value-value
            k = vr.index(value)
            row = [0]*width
            for i, bit in enumerate(z):
                row[h*(n+1)+i] = residue*bit
                row[(m+k)*(n+1)+i] = -residue*bit
            rows.append(row)
        output.append(rows[0])
        constraints.extend([[a-b for a,b in zip(row,rows[0])] for row in rows[1:]])
    return constraints, output


def rational(model, value):
    q = model.eval(value, model_completion=True)
    assert z3.is_rational_value(q)
    return Fraction(q.numerator_as_long(), q.denominator_as_long())


def fit_signs(constraints, output, labels, seconds):
    width = len(output[0])
    theta = [z3.Real(f'theta_{j}') for j in range(width)]
    solver = z3.SolverFor('QF_LRA')
    solver.set(timeout=max(1, int(1000*seconds)))
    def dot(row):
        return z3.Sum([c*t for c,t in zip(row,theta) if c])
    solver.add(*[dot(row) == 0 for row in constraints])
    solver.add(*[y*dot(row) >= 1 for y,row in zip(labels,output)])
    status = solver.check()
    result = {'status':str(status)}
    if status == z3.sat:
        model = solver.model()
        coefficients = [rational(model,t) for t in theta]
        assert all(sum(c*t for c,t in zip(row,coefficients)) == 0 for row in constraints)
        values = [sum(c*t for c,t in zip(row,coefficients)) for row in output]
        margin = min(y*r for y,r in zip(labels,values))
        assert margin >= 1
        result.update(coefficients=list(map(str,coefficients)), labels=labels,
                      output_values=list(map(str,values)), exact_minimum_margin=str(margin))
    elif status == z3.unknown:
        result['reason_unknown'] = solver.reason_unknown()
    return result


def solve(n, m, bound, seconds, trials, seed, out):
    assert n >= 2 and m >= 2
    started = time.monotonic()
    u = [[j]+[z3.Int(f'u_{j}_{i}') for i in range(n)] for j in range(m)]
    v = [[j]+[z3.Int(f'v_{j}_{i}') for i in range(n)] for j in range(m)]
    variables = [t for row in u+v for t in row[1:]]
    solver = z3.SolverFor('QF_LIA')
    solver.set(random_seed=seed)
    solver.add(*[z3.And(-bound <= t, t <= bound) for t in variables])
    # Subtracting the first affine form from both lists preserves matching,
    # distinctness, and the second difference of the minimum root.
    solver.add(*[t == 0 for t in u[0][1:]])
    all_values = []
    for bits in itertools.product((0,1),repeat=n):
        ur, vr = [affine(r,bits) for r in u], [affine(r,bits) for r in v]
        solver.add(z3.Distinct(ur), z3.Distinct(vr))
        solver.add(*[z3.Or([a == b for b in vr]) for a in ur])
        all_values.append((bits,ur,vr))
    for i in range(1,n+1):
        solver.add(z3.Sum([r[i] for r in u]) == z3.Sum([r[i] for r in v]))
    mins = {bits:minimum(ur) for bits,ur,_ in all_values}
    square = [tuple([a,b]+[0]*(n-2)) for a,b in ((0,0),(1,0),(0,1),(1,1))]
    solver.add(mins[square[0]]-mins[square[1]]-mins[square[2]]+mins[square[3]] != 0)
    edges = [[z3.Or([ur[h] == vr[k] for _,ur,vr in all_values]) for k in range(m)]
             for h in range(m)]
    distance = [z3.Int(f'd_{j}') for j in range(2*m)]
    solver.add(distance[0] == 0)
    for j in range(1,2*m):
        solver.add(distance[j] >= 1, distance[j] < 2*m)
        neighbors = ([(m+k,edges[j][k]) for k in range(m)] if j < m else
                     [(h,edges[h][j-m]) for h in range(m)])
        solver.add(z3.Or([z3.And(edge,distance[k] < distance[j]) for k,edge in neighbors]))
    rng = random.Random(seed)
    for trial in range(trials):
        remaining = seconds-(time.monotonic()-started)
        if remaining <= 0 or (out/'STOP').exists():
            break
        solver.set(timeout=max(1,int(remaining*1000)))
        status = solver.check()
        record = {'n':n,'roots':m,'coefficient_bound':bound,'trial':trial,'status':str(status),
                  'elapsed_seconds':time.monotonic()-started,'target_proved':False}
        if status == z3.sat:
            model = solver.model()
            uu = [[row[0]]+[model.eval(t).as_long() for t in row[1:]] for row in u]
            vv = [[row[0]]+[model.eval(t).as_long() for t in row[1:]] for row in v]
            record.update(u=uu,v=vv,identity_audit=verify_identity(uu,vv))
            constraints,output = tangent_rows(uu,vv)
            rank_c = fmpq_mat(constraints).rank()
            rank_cr = fmpq_mat(constraints+output).rank()
            record.update(exact_constraint_rank=rank_c,exact_combined_rank=rank_cr,
                          exact_output_dimension=rank_cr-rank_c)
            if rank_cr > rank_c:
                parity = [(-1)**sum(bits) for bits in itertools.product((0,1),repeat=n)]
                labels = [rng.choice((-1,1)) for _ in parity]
                record['parity_fit'] = fit_signs(constraints,output,parity,30)
                record['random_fit'] = fit_signs(constraints,output,labels,30)
            solver.add(z3.Or([t != model.eval(t) for t in variables]))
        elif status == z3.unknown:
            record['reason_unknown'] = solver.reason_unknown()
        path = out/f'n{n}-m{m}-trial{trial}.json'
        path.write_text(json.dumps(record,indent=2)+'\n')
        print(json.dumps({k:v for k,v in record.items()
                          if k not in ('u','v','parity_fit','random_fit')}),flush=True)
        if status != z3.sat:
            break


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n',type=int,required=True)
    parser.add_argument('--roots',type=int,required=True)
    parser.add_argument('--bound',type=int,default=12)
    parser.add_argument('--seconds',type=float,default=7200)
    parser.add_argument('--trials',type=int,default=32)
    parser.add_argument('--seed',type=int,default=2026112314)
    parser.add_argument('--out',type=Path,required=True)
    args = parser.parse_args(); args.out.mkdir(parents=True,exist_ok=True)
    solve(args.n,args.roots,args.bound,args.seconds,args.trials,args.seed,args.out)


if __name__ == '__main__':
    main()
