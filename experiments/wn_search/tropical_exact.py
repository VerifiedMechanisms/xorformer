#!/usr/bin/env python3
"""Exact decision procedure (SAT, python-sat / CaDiCaL) for the tropical (dominance) head model.

Model.  n input bits; the nonzero points x in {0,1}^n \\ {0}.  Head h has a permutation pi_h of the
coordinates (pi_h(k) = coordinate at position k, k = 1..n); its n rules are
    R(h,k) = {x : x_{pi_h(k)} = 1 and x_{pi_h(j)} = 0 for all j < k},
i.e. x in R(h,k) iff k is the first position of pi_h that meets supp(x).  There is a global strict
total order (priority) on the nH rules and a sign c(h,k) in {+1,-1} per rule; the output at x is the
sign of the highest-priority rule among the H rules containing x.  T(f) = min H such that f is
representable.

SAT encoding (0-based positions k = 0..n-1, coordinates i = 0..n-1, rule index a = h*n + k):
  p[h,k,i]   pi_h(k) = i                               (exactly-one per row and per column)
  u[h,k,i]   i is among the first k+1 positions of pi_h (u[h,k,i] <-> u[h,k-1,i] or p[h,k,i])
  cov[h,k,x] prefix of length k+1 meets supp(x)         (cov <-> OR_{i in supp x} u[h,k,i])
  r[h,k,x]   x in R(h,k)                                (r <-> cov[h,k,x] and not cov[h,k-1,x])
  c[a]       sign of rule a (true = +1)
  bef[a,b]   a has higher priority than b (one variable per unordered pair; transitivity clauses
             forbid the two cyclic orientations of every triple -> strict total order)
  win[a,x]   a is the highest-priority rule containing x:
             win -> r[a,x];  win -> (c[a] == f(x));  win and r[b,x] -> bef[a,b]  (b in other heads);
             for every x: OR_a win[a,x].
  Symmetry breaking: heads are interchangeable, so pi_1 <=lex pi_2 <=lex ... <=lex pi_H.
A point of weight w can only lie in rules with k <= n-w, which removes the corresponding variables.
Every SAT model is decoded and re-checked by an independent simulator (evaluate()).

Brute force (for verification):
  * naive_bruteforce(n=3): all multisets of permutations x all (nH)! priority orders; signs are not
    enumerated because for a fixed order f is representable iff f is constant on every fiber of the
    "top rule" map (then the sign of each rule is forced) -- this is equivalent to enumerating signs.
  * greedy_bruteforce: all multisets of permutations, and for each an exact decision-list test
    (a rule can be placed next iff it is monochromatic on the still-uncovered points; placing a rule
    never destroys placeability of another, so greedy is complete -- Rivest's argument).

Usage:
  python3 tropical_exact.py selftest                        # n=3, all 128 targets, SAT vs brute force
  python3 tropical_exact.py run --n 4 --nrand 30 --timeout 600
  python3 tropical_exact.py run --n 6 --nrand 5 --timeout 600 --targets random,parity
  python3 tropical_exact.py bf --n 4 --nrand 30 --Hmax 6     # greedy brute force cross-check
"""
import argparse
import itertools
import json
import multiprocessing as mp
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def popcount(x):
    return bin(x).count('1')


def support(x, n):
    return [i for i in range(n) if (x >> i) & 1]


def nonzero_points(n):
    return list(range(1, 2 ** n))


# ----------------------------------------------------------------------------- targets
def target_parity(n):
    return {x: (1 if popcount(x) % 2 == 1 else -1) for x in nonzero_points(n)}


def target_majority(n, weak=False):
    # strict: +1 iff |x| > n/2 ; weak (even n only differs): +1 iff |x| >= n/2
    return {x: (1 if (popcount(x) >= n / 2 if weak else popcount(x) > n / 2) else -1)
            for x in nonzero_points(n)}


def target_random(n, rng):
    return {x: int(rng.choice([-1, 1])) for x in nonzero_points(n)}


def make_targets(n, nrand, seed, which):
    rng = np.random.default_rng(seed)
    out = []
    if 'random' in which:
        for t in range(nrand):
            out.append((f'random{t}', target_random(n, rng)))
    if 'parity' in which:
        out.append(('parity', target_parity(n)))
    if 'majority' in which:
        out.append(('majority', target_majority(n)))
        if n % 2 == 0:
            out.append(('majority_weak', target_majority(n, weak=True)))
    return out


def fkey(n, f):
    return ''.join('+' if f[x] == 1 else '-' for x in nonzero_points(n))


# ----------------------------------------------------------------------------- simulator
def rule_of(pi, x):
    """0-based position k of the first coordinate of pi meeting supp(x)."""
    for k, i in enumerate(pi):
        if (x >> i) & 1:
            return k
    raise ValueError('x = 0 has no rule')


def evaluate(n, perms, rank, signs):
    """perms[h] = tuple of coordinates; rank[(h,k)] = priority rank (smaller = higher);
    signs[(h,k)] in {+1,-1}.  Returns dict x -> output sign."""
    out = {}
    for x in nonzero_points(n):
        best = None
        for h, pi in enumerate(perms):
            a = (h, rule_of(pi, x))
            if best is None or rank[a] < rank[best]:
                best = a
        out[x] = signs[best]
    return out


# ----------------------------------------------------------------------------- SAT encoding
class TropicalCNF:
    def __init__(self, n, H, f, lex=True, amo_win=False, alo_rule=True):
        self.n, self.H, self.f = n, H, f
        self.nv = 0
        self.clauses = []
        self.TRUE = self.new()
        self.clauses.append([self.TRUE])
        pts = nonzero_points(n)
        wt = {x: popcount(x) for x in pts}
        S = {x: support(x, n) for x in pts}
        R = H * n
        new, add, T = self.new, self.add, self.TRUE

        # --- permutations: p one-hot, u prefix membership
        p = {(h, k, i): new() for h in range(H) for k in range(n) for i in range(n)}
        for h in range(H):
            for k in range(n):
                self.exactly_one([p[h, k, i] for i in range(n)])
            for i in range(n):
                self.exactly_one([p[h, k, i] for k in range(n)])
        u = {}
        for h in range(H):
            for i in range(n):
                for k in range(n):
                    if k == 0:
                        u[h, k, i] = p[h, 0, i]
                    elif k == n - 1:
                        u[h, k, i] = T
                    else:
                        v = new()
                        u[h, k, i] = v
                        # v <-> u[k-1] or p[k]
                        add([-v, u[h, k - 1, i], p[h, k, i]])
                        add([v, -u[h, k - 1, i]])
                        add([v, -p[h, k, i]])
        for h in range(H):
            for i in range(n):  # u[h,n-1,i] = TRUE must be consistent: u[h,n-2,i] or p[h,n-1,i]
                add([u[h, n - 2, i], p[h, n - 1, i]])

        # --- cov and r (rule membership) per head and point
        cov = {}
        r = {}
        for h in range(H):
            for x in pts:
                w = wt[x]
                for k in range(n):
                    if k >= n - w:
                        cov[h, k, x] = T
                    elif w == 1:
                        cov[h, k, x] = u[h, k, S[x][0]]
                    else:
                        v = new()
                        cov[h, k, x] = v
                        lits = [u[h, k, i] for i in S[x]]
                        add([-v] + lits)
                        for l in lits:
                            add([v, -l])
                for k in range(n):
                    if k > n - w:
                        r[h, k, x] = -T
                    elif k == 0:
                        r[h, k, x] = cov[h, 0, x]
                    elif cov[h, k, x] == T:
                        r[h, k, x] = -cov[h, k - 1, x]
                    else:
                        v = new()
                        r[h, k, x] = v
                        add([-v, cov[h, k, x]])
                        add([-v, -cov[h, k - 1, x]])
                        add([v, -cov[h, k, x], cov[h, k - 1, x]])
                if alo_rule:
                    add([r[h, k, x] for k in range(n - w + 1)])

        # --- signs and priority order
        c = {a: new() for a in range(R)}
        bef = {(a, b): new() for a in range(R) for b in range(a + 1, R)}

        def lit(a, b):
            return bef[a, b] if a < b else -bef[b, a]

        for a in range(R):
            for b in range(a + 1, R):
                for d in range(b + 1, R):
                    add([-lit(a, b), -lit(b, d), lit(a, d)])
                    add([lit(a, b), lit(b, d), -lit(a, d)])

        # --- winners
        win = {}
        for x in pts:
            w = wt[x]
            cands = [(h, k) for h in range(H) for k in range(n - w + 1)]
            for (h, k) in cands:
                v = new()
                win[h, k, x] = v
                a = h * n + k
                add([-v, r[h, k, x]])
                add([-v, c[a] if f[x] == 1 else -c[a]])
                for (h2, k2) in cands:
                    if h2 != h:
                        add([-v, -r[h2, k2, x], lit(a, h2 * n + k2)])
            add([win[h, k, x] for (h, k) in cands])
            if amo_win:
                vs = [win[h, k, x] for (h, k) in cands]
                for i1 in range(len(vs)):
                    for i2 in range(i1 + 1, len(vs)):
                        add([-vs[i1], -vs[i2]])

        # --- symmetry breaking: pi_h <=lex pi_{h+1}
        if lex:
            for h in range(H - 1):
                e_prev = T  # prefixes of length 0 are equal
                for k in range(n - 1):
                    for i in range(n):
                        for i2 in range(i):
                            add([-e_prev, -p[h, k, i], -p[h + 1, k, i2]])
                    if k <= n - 3:
                        e = new()
                        add([-e, e_prev])
                        for i in range(n):
                            add([-e, -p[h, k, i], p[h + 1, k, i]])
                            add([-e_prev, -p[h, k, i], -p[h + 1, k, i], e])
                        e_prev = e

        self.p, self.c, self.bef, self.lit, self.win, self.r = p, c, bef, lit, win, r

    def new(self):
        self.nv += 1
        return self.nv

    def add(self, clause):
        if self.TRUE in clause:
            return
        clause = [l for l in clause if l != -self.TRUE]
        self.clauses.append(clause)

    def exactly_one(self, lits):
        self.add(list(lits))
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                self.add([-lits[i], -lits[j]])

    def decode(self, model):
        val = set(l for l in model if l > 0)
        n, H, R = self.n, self.H, self.n * self.H
        perms = []
        for h in range(H):
            pi = []
            for k in range(n):
                js = [i for i in range(n) if self.p[h, k, i] in val]
                assert len(js) == 1
                pi.append(js[0])
            assert sorted(pi) == list(range(n))
            perms.append(tuple(pi))

        def tv(l):
            return (l in val) if l > 0 else (-l not in val)

        rank = {}
        for a in range(R):
            rank[divmod(a, n)] = sum(1 for b in range(R) if b != a and tv(self.lit(b, a)))
        assert sorted(rank.values()) == list(range(R)), 'priority order is not total'
        signs = {divmod(a, n): (1 if self.c[a] in val else -1) for a in range(R)}
        return perms, rank, signs


def _child_solve(n, H, f, solver_name, opts, conn):
    t0 = time.time()
    enc = TropicalCNF(n, H, f, **opts)
    t_enc = time.time() - t0
    from pysat.solvers import Solver
    with Solver(name=solver_name, bootstrap_with=enc.clauses) as s:
        res = s.solve()
        model = s.get_model() if res else None
    out = {'status': 'SAT' if res else 'UNSAT', 'nv': enc.nv, 'ncl': len(enc.clauses), 't_enc': t_enc}
    if res:
        perms, rank, signs = enc.decode(model)
        out['model'] = (perms, {f'{h},{k}': v for (h, k), v in rank.items()},
                        {f'{h},{k}': v for (h, k), v in signs.items()})
    conn.send(out)
    conn.close()


def representable(n, f, H, timeout=600, solver_name='cadical153', **opts):
    """Exact decision: returns dict with status in {SAT, UNSAT, TIMEOUT}, time, and a verified model."""
    t0 = time.time()
    parent, child = mp.Pipe(duplex=False)
    pr = mp.Process(target=_child_solve, args=(n, H, f, solver_name, opts, child))
    pr.start()
    child.close()
    res = None
    if parent.poll(timeout):
        res = parent.recv()
    pr.join(1)
    if pr.is_alive():
        pr.terminate()
        pr.join()
    dt = time.time() - t0
    if res is None:
        return {'status': 'TIMEOUT', 'time': dt}
    res['time'] = dt
    if res['status'] == 'SAT':
        perms, rank_s, signs_s = res['model']
        rank = {tuple(map(int, k.split(','))): v for k, v in rank_s.items()}
        signs = {tuple(map(int, k.split(','))): v for k, v in signs_s.items()}
        out = evaluate(n, perms, rank, signs)
        assert all(out[x] == f[x] for x in nonzero_points(n)), 'decoded model does not realize f (bug)'
        res['verified'] = True
    return res


def min_heads(n, f, Hmax, timeout=600, H0=1, solver_name='cadical153', log=None, **opts):
    """Search for T(f).  Ascend H = H0, H0+1, ... until the first SAT; if the very first call (H0 > 1)
    is already SAT, descend to confirm (UNSAT at H-1 proves optimality).  Representability is
    monotone in H (an extra head can be put at the bottom of the priority), so UNSAT at H proves
    T(f) > H.  Returns per-H statuses and the bracket lo <= T(f) <= hi (proved iff lo == hi)."""
    per_H = {}

    def solve(H):
        res = representable(n, f, H, timeout=timeout, solver_name=solver_name, **opts)
        per_H[H] = res
        if log:
            log(f'    H={H}: {res["status"]} [{res["time"]:.1f}s]')
        return res['status']

    H = H0
    while H <= Hmax and solve(H) != 'SAT':
        H += 1
    hi = H if H <= Hmax else None
    if hi is not None and hi == H0 and H0 > 1:   # started too high: descend to confirm
        H, budget = H0 - 1, 2                      # at most two consecutive timeouts below the last SAT
        while H >= 1 and budget > 0:
            st = solve(H)
            if st == 'SAT':
                hi, budget = H, 2
            elif st == 'UNSAT':
                break
            else:
                budget -= 1
            H -= 1
    lo = 1 + max([H for H, r in per_H.items() if r['status'] == 'UNSAT'], default=0)
    return {'per_H': {H: {'status': r['status'], 'time': round(r['time'], 2)} for H, r in sorted(per_H.items())},
            'lo': lo, 'hi': hi, 'proved': (hi is not None and lo == hi),
            'model': per_H[hi].get('model') if hi is not None else None}


# ----------------------------------------------------------------------------- brute force
def rule_masks(n, pi, pts):
    """bitmask over point indices of each rule R(h,k) of permutation pi."""
    masks = [0] * n
    for j, x in enumerate(pts):
        masks[rule_of(pi, x)] |= 1 << j
    return masks


def greedy_ok(rules, plus, full):
    """Exact test for fixed rules: does some priority order + signs realize f (plus = +1 points)?"""
    unc = full
    changed = True
    while unc and changed:
        changed = False
        for R in rules:
            part = R & unc
            if part and ((part & plus) == part or (part & plus) == 0):
                unc &= ~R
                changed = True
    return unc == 0


def greedy_bruteforce(n, f, Hmax):
    """Exact T(f) by enumerating all multisets of H permutations (H = 1..Hmax) + greedy test."""
    pts = nonzero_points(n)
    perms = list(itertools.permutations(range(n)))
    masks = [rule_masks(n, pi, pts) for pi in perms]
    plus = sum(1 << j for j, x in enumerate(pts) if f[x] == 1)
    full = (1 << len(pts)) - 1
    for H in range(1, Hmax + 1):
        for combo in itertools.combinations_with_replacement(range(len(perms)), H):
            rules = [m for ci in combo for m in masks[ci]]
            if greedy_ok(rules, plus, full):
                return H
    return None


def naive_bruteforce(n=3, Hmax=3):
    """All multisets of H permutations x all (nH)! priority orders.  For each configuration the
    top-rule map partitions the points into fibers; f is representable with this configuration iff
    f is constant on each fiber (then signs are forced).  Returns {H: set of representable f},
    f encoded as bitmask of +1 points."""
    pts = nonzero_points(n)
    P = len(pts)
    perms = list(itertools.permutations(range(n)))
    masks = [rule_masks(n, pi, pts) for pi in perms]
    rep = {}
    for H in range(1, Hmax + 1):
        R = H * n
        ranks = np.array(list(itertools.permutations(range(R))), dtype=np.int16)  # (R!, R)
        reps = set()
        for combo in itertools.combinations_with_replacement(range(len(perms)), H):
            rules = [m for ci in combo for m in masks[ci]]
            M = np.array([[(rules[a] >> j) & 1 for j in range(P)] for a in range(R)], dtype=bool)
            winner = np.empty((ranks.shape[0], P), dtype=np.int16)
            for j in range(P):
                rk = np.where(M[:, j][None, :], ranks, R + 1)
                winner[:, j] = rk.argmin(axis=1)
            for part in np.unique(winner, axis=0):
                fibers = {}
                for j in range(P):
                    fibers[int(part[j])] = fibers.get(int(part[j]), 0) | (1 << j)
                fl = list(fibers.values())
                for choice in range(1 << len(fl)):
                    fm = 0
                    for t, m in enumerate(fl):
                        if (choice >> t) & 1:
                            fm |= m
                    reps.add(fm)
        rep[H] = reps
    return rep


# ----------------------------------------------------------------------------- drivers
def selftest(timeout=600, solver_name='cadical153', **opts):
    n = 3
    pts = nonzero_points(n)
    t0 = time.time()
    rep = naive_bruteforce(n, 3)
    print(f'naive brute force n=3 (perms x orders): representable counts: '
          f'{ {H: len(s) for H, s in rep.items()} } [{time.time()-t0:.1f}s]', flush=True)
    all_f = []
    for fm in range(1 << len(pts)):
        all_f.append({x: (1 if (fm >> j) & 1 else -1) for j, x in enumerate(pts)})
    t0 = time.time()
    Tg = [greedy_bruteforce(n, f, 5) for f in all_f]
    print(f'greedy brute force n=3: T distribution: { {T: Tg.count(T) for T in sorted(set(Tg), key=lambda t: (t is None, t))} } '
          f'[{time.time()-t0:.1f}s]', flush=True)
    # SAT decisions for every f and H = 1,2,3 (and 4,5 if needed)
    t0 = time.time()
    agree = 0
    total = 0
    Tsat = []
    for fm, f in enumerate(all_f):
        Hs = [1, 2, 3]
        res = {}
        for H in Hs:
            res[H] = representable(n, f, H, timeout=timeout, solver_name=solver_name, **opts)['status']
            naive = 'SAT' if fm in rep[H] else 'UNSAT'
            total += 1
            if res[H] == naive:
                agree += 1
            else:
                print(f'  DISAGREEMENT f={fkey(n, f)} H={H}: sat={res[H]} naive={naive}')
        T = next((H for H in Hs if res[H] == 'SAT'), None)
        if T is None:
            for H in (4, 5):
                if representable(n, f, H, timeout=timeout, solver_name=solver_name, **opts)['status'] == 'SAT':
                    T = H
                    break
        Tsat.append(T)
    print(f'SAT vs naive brute force (n=3, 128 targets x H=1,2,3): {agree}/{total} decisions agree '
          f'[{time.time()-t0:.1f}s]')
    mism = sum(1 for a, b in zip(Tsat, Tg) if a != b)
    print(f'SAT T(f) vs greedy brute force T(f): {128 - mism}/128 agree; T distribution (SAT): '
          f'{ {T: Tsat.count(T) for T in sorted(set(Tsat), key=lambda t: (t is None, t))} }')
    print('examples: parity', fkey(n, target_parity(n)), 'T =', Tsat[sum(1 << j for j, x in enumerate(pts) if target_parity(n)[x] == 1)],
          '; majority', fkey(n, target_majority(n)), 'T =', Tsat[sum(1 << j for j, x in enumerate(pts) if target_majority(n)[x] == 1)])


def run(args):
    n = args.n
    which = args.targets.split(',')
    targets = make_targets(n, args.nrand, args.seed, which)
    if args.only:
        targets = [t for t in targets if t[0] in args.only.split(',')]
    opts = dict(lex=not args.no_lex, amo_win=args.amo_win, alo_rule=not args.no_alo)
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
    out_path = args.out or os.path.join(HERE, 'results', f'tropical_exact_n{n}{args.tag}.jsonl')
    N = 2 ** n
    for name, f in targets:
        print(f'n={n} target={name} f={fkey(n, f)}', flush=True)
        t0 = time.time()
        res = min_heads(n, f, args.Hmax, timeout=args.timeout, H0=args.H0, solver_name=args.solver,
                        log=lambda s: print(s, flush=True), **opts)
        dt = time.time() - t0
        T = res['hi']
        status = ('T = %d (proved)' % T) if res['proved'] else (
            'T in [%d, %s]' % (res['lo'], T if T is not None else f'>{args.Hmax}'))
        print(f'  => {name}: {status}; N/n^2 = {N / n / n:.2f}, N/n = {N / n:.2f} [{dt:.0f}s]', flush=True)
        rec = {'n': n, 'target': name, 'f': fkey(n, f), 'lo': res['lo'], 'hi': T, 'proved': res['proved'],
               'per_H': res['per_H'], 'time': round(dt, 1), 'solver': args.solver, 'opts': opts,
               'model': res['model']}
        with open(out_path, 'a') as fh:
            fh.write(json.dumps(rec) + '\n')


def bf(args):
    n = args.n
    targets = make_targets(n, args.nrand, args.seed, args.targets.split(','))
    if args.only:
        targets = [t for t in targets if t[0] in args.only.split(',')]
    for name, f in targets:
        t0 = time.time()
        T = greedy_bruteforce(n, f, args.Hmax)
        print(f'bf n={n} target={name} f={fkey(n, f)} T={T if T is not None else ">%d" % args.Hmax} '
              f'[{time.time()-t0:.0f}s]', flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['selftest', 'run', 'bf'])
    ap.add_argument('--n', type=int, default=4)
    ap.add_argument('--nrand', type=int, default=30)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--targets', default='random,parity,majority')
    ap.add_argument('--only', default='')
    ap.add_argument('--Hmax', type=int, default=16)
    ap.add_argument('--H0', type=int, default=1)
    ap.add_argument('--timeout', type=float, default=600)
    ap.add_argument('--solver', default='cadical153')
    ap.add_argument('--no-lex', action='store_true')
    ap.add_argument('--no-alo', action='store_true')
    ap.add_argument('--amo-win', action='store_true')
    ap.add_argument('--out', default='')
    ap.add_argument('--tag', default='')
    args = ap.parse_args()
    if args.mode == 'selftest':
        selftest(timeout=args.timeout, solver_name=args.solver,
                 lex=not args.no_lex, amo_win=args.amo_win, alo_rule=not args.no_alo)
    elif args.mode == 'run':
        run(args)
    else:
        bf(args)


if __name__ == '__main__':
    main()
