#!/usr/bin/env python3
"""Small exact checks of reverse-axis interpolation and audited gluing.

This is a finite regression check, not evidence of asymptotic universality.
Every calculation uses Fraction. No numerical optimizer is used.
"""

from fractions import Fraction as Q
from itertools import product
import json
import random


def cube(n):
    return list(product((0, 1), repeat=n))


def affine(a, x):
    return a[0] + sum(c * b for c, b in zip(a[1:], x))


def value(heads, x):
    return sum((Q(affine(a, x), affine(b, x)) for a, b in heads), Q(0))


def local(table):
    r, s = len(table), len(table[0])
    m = r + s
    scale = m * (m - 1)
    base = [m + 2] + [-1] * m
    heads = []
    total = [0] * (m + 1)
    for i in range(r):
        a = [0] + [0] * r + [scale * v for v in table[i]]
        b = base.copy()
        b[1 + i] -= 1
        heads.append((a, b))
        total = [u + v for u, v in zip(total, a)]
    heads.append(([-v for v in total], base))
    return heads


def check_local():
    cases = 0
    for r, s in [(1, 1), (1, 3), (2, 2), (2, 3), (3, 3)]:
        for signs in product((-1, 1), repeat=r * s):
            table = [signs[s * i:s * (i + 1)] for i in range(r)]
            heads = local(table)
            assert len(heads) == r + 1
            for a, b in heads:
                assert all(c < 0 for c in b[1:])
                assert min(affine(b, x) for x in cube(r + s)) >= 1
            for x in cube(r + s):
                if not any(x[:r]) or not any(x[r:]):
                    assert value(heads, x) == 0
            for i in range(r):
                for j in range(s):
                    x = tuple(int(k == i or k == r + j) for k in range(r + s))
                    assert value(heads, x) == table[i][j]
            cases += 1
    return cases


def open_cover(n):
    """Greedy cover only for regression tests, not the asymptotic cover proof."""
    uncovered = set(range((1 << n) - 1))
    centers = []
    while uncovered:
        def children(s):
            return {s ^ (1 << i) for i in range(n) if s & (1 << i)}
        s = max(range(1, 1 << n), key=lambda t: (len(children(t) & uncovered), t))
        centers.append(s)
        uncovered -= children(s)
    return centers


def ambient_module(n, a, s, t, labels):
    rows = [i for i in range(a) if s & (1 << i)]
    cols = [a + j for j in range(n - a) if t & (1 << j)]
    active = rows + cols
    cell = []
    table = []
    for i in rows:
        line = []
        for j in cols:
            x = tuple(int(k in active and k not in (i, j)) for k in range(n))
            line.append(labels[x])
            cell.append(x)
        table.append(line)
    result = []
    for numerator, denominator in local(table):
        forms = []
        for form in (numerator, denominator):
            out = [form[0] + sum(form[1:])] + [0] * n
            for k, coeff in zip(active, form[1:]):
                out[1 + k] = -coeff
            forms.append(out)
        for k in range(n):
            if k not in active:
                forms[1][1 + k] = 1
        result.append(tuple(forms))
    return result, set(cell), set(active)


def ceil_q(q):
    return -((-q.numerator) // q.denominator)


def glue_test(n, seed):
    rng = random.Random(seed)
    xs = cube(n)
    labels = {x: rng.choice((-1, 1)) for x in xs}
    a = n // 2
    centers = list(product(open_cover(a), open_cover(n - a)))
    # Random ties specifically exercise the proof's arbitrary tie breaking.
    rng.shuffle(centers)
    centers.sort(key=lambda st: -(st[0].bit_count() + st[1].bit_count()))
    protected, score = set(), []
    for s, t in centers:
        heads, cell, active = ambient_module(n, a, s, t, labels)
        # Introduce a genuine nonzero local bias, then absorb it before penalty.
        bias = 7
        aa, bb = heads[0]
        biased_a = [u - bias * v for u, v in zip(aa, bb)]
        biased_heads = [(biased_a, bb)] + heads[1:]
        assert all(bias + value(biased_heads, x) == value(heads, x) for x in xs)
        heads[0] = ([u + bias * v for u, v in zip(biased_a, bb)], bb)
        old = {x: value(score, x) for x in protected | cell}
        lam = 1 + max(0, *(ceil_q(-old[x] / value(heads, x)) for x in cell))
        outside = [x for x in protected if any(x[k] for k in range(n) if k not in active)]
        penalty = 1
        for x in outside:
            q = sum(x[k] for k in range(n) if k not in active)
            bound = Q(lam * sum(abs(affine(aa, x)) for aa, _ in heads), q) / abs(old[x])
            penalty = max(penalty, 1 + ceil_q(bound))
        added = []
        for aa, bb in heads:
            new_b = bb.copy()
            for k in range(n):
                if k not in active:
                    new_b[1 + k] += penalty
            assert new_b[0] > 0 and all(v > 0 for v in new_b[1:])
            added.append(([lam * v for v in aa], new_b))
        score.extend(added)
        protected |= cell
        assert all(labels[x] * value(score, x) > 0 for x in protected)
    expected = {x for x in xs if not all(x[:a]) and not all(x[a:])}
    assert protected == expected
    # Exact face repair first; its monomials are approximated below.
    def coefficients(vals, k):
        c = vals.copy()
        for bit in range(k):
            for mask in range(1 << k):
                if mask & (1 << bit):
                    c[mask] -= c[mask ^ (1 << bit)]
        return c
    corrections = []
    def monomial(v, x):
        return int(all(x[k] for k in v))
    for fixed, free in [(list(range(a)), list(range(a, n))),
                        (list(range(a, n)), list(range(a)))]:
        vals = []
        for mask in range(1 << len(free)):
            x = tuple(int(k in fixed or (k in free and bool(mask & (1 << free.index(k))))) for k in range(n))
            vals.append(labels[x] - value(score, x) -
                        sum(c * monomial(v, x) for v, c in corrections))
        for mask, c in enumerate(coefficients(vals, len(free))):
            v = set(fixed) | {k for j, k in enumerate(free) if mask & (1 << j)}
            corrections.append((v, c))
    formal = {x: value(score, x) + sum(c * monomial(v, x) for v, c in corrections) for x in xs}
    assert all(labels[x] * formal[x] > 0 for x in xs)
    assert len(corrections) == 2 ** a + 2 ** (n - a)
    margin = min(labels[x] * formal[x] for x in xs)
    mass = sum(abs(c) for _, c in corrections)
    eta = min(Q(1, 2), margin / (4 * n * (mass + 1)))
    for v, c in corrections:
        weights = [Q(1) if k in v else eta * eta for k in range(n)]
        score.append(([c * eta] + [0] * n, [eta + sum(weights)] + [-w for w in weights]))
    assert all(labels[x] * value(score, x) > 0 for x in xs)
    return {"n": n, "seed": seed, "modules": len(centers), "heads": len(score),
            "correction_heads": len(corrections), "strict_signs": 2 ** n}


def check_wrong_order():
    labels = {x: 1 for x in cube(4)}
    zero = (0, 0, 0, 0)
    labels[zero] = -1
    old, _, _ = ambient_module(4, 2, 1, 1, labels)
    new, _, _ = ambient_module(4, 2, 3, 3, labels)
    target = (0, 1, 0, 1)
    assert value(old, zero) == -1 and value(new, zero) == 24
    assert value(old, target) == -Q(1, 6) and value(new, target) == 1
    # The target requires lambda > 1/6, preservation requires lambda < 1/24.
    assert Q(1, 24) < Q(1, 6)
    return {"wrong_order": "singleton centers before full centers",
            "new_cell_requires_lambda_gt": "1/6",
            "protected_zero_requires_lambda_lt": "1/24",
            "scalar_repair_possible": False}


if __name__ == "__main__":
    result = {"arithmetic": "exact fractions", "local_sign_tables": check_local(),
              "gluing": [glue_test(n, seed) for n in (2, 3, 4) for seed in range(3)],
              "ordering_counterexample": check_wrong_order(),
              "asymptotic_compiler_proved": False}
    print(json.dumps(result, indent=2))
