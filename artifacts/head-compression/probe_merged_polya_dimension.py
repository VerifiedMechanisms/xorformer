"""Search for flexible merged positive-step Polya refinement graphs.

Each internal state p has children p + delta*e_i for every color i, with
one common positive delta. Equal integer states are merged. For each
resulting graph we compute the dimension of its linear realization space,
and, for a potential excess, its projection to the root/terminal states.
This tests a new structural question; it is not a head-bound proof.
"""
import argparse
from collections import deque
import json
from pathlib import Path
import random
import time

from flint import nmod_mat, fmpq_mat


class DSU:
    def __init__(self, n):
        self.parent = list(range(n))

    def find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, x, y):
        x, y = self.find(x), self.find(y)
        if x != y:
            self.parent[y] = x


def graph(rng, d, height, roots, stop, cap):
    states, index, todo = [], {}, deque()

    def insert(p):
        if p not in index:
            index[p] = len(states)
            states.append(p)
            todo.append(index[p])
        return index[p]

    insert((0,) * d)
    for _ in range(roots - 1):
        insert(tuple(rng.randrange(3) for _ in range(d)))
    stars = []
    while todo:
        v = todo.popleft()
        p = states[v]
        remaining = height - sum(p)
        if remaining <= 0 or len(states) + d > cap or rng.random() < stop:
            continue
        delta = 1 if rng.random() < .7 else rng.randint(1, remaining)
        children = []
        for i in range(d):
            q = list(p)
            q[i] += delta
            children.append(insert(tuple(q)))
        stars.append((v, tuple(children), delta))
    return states, stars


def dimensions(states, stars):
    d, V = len(states[0]), len(states)
    incoming = [0] * V
    internal = set()
    eq = DSU(V * d)
    for v, children, delta in stars:
        internal.add(v)
        assert delta > 0
        for i, w in enumerate(children):
            incoming[w] += 1
            assert all(states[w][j] - states[v][j] == (delta if i == j else 0)
                       for j in range(d))
            for j in range(d):
                if j != i:
                    eq.union(v * d + j, w * d + j)
    components = {eq.find(j) for j in range(V * d)}
    ids = {c: j for j, c in enumerate(sorted(components))}
    C = len(ids)
    rows = []
    for v, children, _ in stars:
        for i in range(1, d):
            row = [0] * C
            for vertex, coordinate, sign in ((children[i], i, 1), (v, i, -1),
                                              (children[0], 0, -1), (v, 0, 1)):
                row[ids[eq.find(vertex * d + coordinate)]] += sign
            rows.append(row)
    roots = {v for v in range(V) if incoming[v] == 0}
    leaves = set(range(V)) - internal
    # Unrefined isolated roots are not cancellation identities and are excluded.
    isolated = roots & leaves
    charged = (roots | leaves) - isolated
    active_components = {ids[eq.find(v * d + i)] for v in set(range(V)) - isolated for i in range(d)}
    cols = sorted(active_components)
    rows = [[row[j] for j in cols] for row in rows]
    C = len(cols)
    if not rows:
        return dict(active=False)
    prime = 1000000007
    rank = nmod_mat(rows, prime).rank()
    upper_dim = C - rank
    result = dict(active=True, colors=d, vertices=V-len(isolated),
                  internal=len(internal), roots=len(roots-isolated),
                  leaves=len(leaves-isolated), charged_heads=len(charged),
                  coordinate_components=C, modular_rank=rank,
                  modular_dimension_upper_bound=upper_dim, prime=prime)
    if upper_dim > len(charged):
        mat = fmpq_mat(rows)
        exact_rank = mat.rref()[1]
        boundary_components = {ids[eq.find(v * d + i)] for v in charged for i in range(d)}
        free_positions = [j for j, original in enumerate(cols) if original not in boundary_components]
        free_rank = fmpq_mat([[row[j] for j in free_positions] for row in rows]).rref()[1] if free_positions else 0
        projected_dimension = C - exact_rank - len(free_positions) + free_rank
        result.update(exact_rank=exact_rank, projected_dimension=projected_dimension,
                      excess=projected_dimension-len(charged),
                      states=states, stars=stars)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seconds', type=float, default=3600)
    p.add_argument('--seed', type=int, default=2026112318)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    rng = random.Random(args.seed)
    started = time.monotonic()
    best, tested, excesses, events = None, 0, [], []
    try:
        while time.monotonic() - started < args.seconds and not (args.out/'STOP').exists():
            d = rng.choice((2, 3, 4, 5, 6))
            height = rng.randint(3, 18)
            states, stars = graph(rng, d, height, rng.randint(1, 4),
                                  rng.choice((0., .05, .15, .3)), 220)
            result = dimensions(states, stars)
            if not result['active']:
                continue
            tested += 1
            ratio = result['modular_dimension_upper_bound'] / result['charged_heads']
            if best is None or ratio > best['ratio']:
                best = dict(result, ratio=ratio, trial=tested)
                print(json.dumps(dict(event='best', **best)), flush=True)
            if result.get('excess', 0) > 0:
                excesses.append(result)
                print(json.dumps(dict(event='exact-excess', **result)), flush=True)
                break
            if tested % 1000 == 0:
                event = dict(trials=tested, elapsed_seconds=time.monotonic()-started,
                             best_ratio=best['ratio'])
                events.append(event)
                print(json.dumps(event), flush=True)
    finally:
        result = dict(scope='Finite structural diagnostic only; universal target unproved.',
                      seed=args.seed, trials=tested, elapsed_seconds=time.monotonic()-started,
                      best=best, exact_excesses=excesses, events=events)
        (args.out/'result.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
