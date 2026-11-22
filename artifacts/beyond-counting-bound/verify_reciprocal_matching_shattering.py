"""Exact finite audits of the reciprocal Hall selector construction.

These verify the formula and selected witnesses. The general Hall proof is
separate. No numerical result is treated as a worst-case head lower bound.
"""
from fractions import Fraction as Q
import itertools
import json
from pathlib import Path
import random


def check(q, modulus, trials):
    s = q.bit_length() - 1
    assert q == 2 ** s

    def mul(a, b):
        out = 0
        while b:
            if b & 1:
                out ^= a
            b >>= 1
            a <<= 1
            if a & q:
                a ^= modulus
        return out

    table = [[mul(a, b) for b in range(q)] for a in range(q)]
    assert all(1 in table[a] for a in range(1, q))
    assert all(table[table[a][b]][c] == table[a][table[b][c]]
               for a, b, c in itertools.product(range(q), repeat=3))
    points = list(itertools.product(range(q), repeat=2))
    colors = [[x ^ table[d][y] for x, y in points] for d in range(q)]
    colors.append([y for x, y in points])
    colors = [row for row in colors for _ in range(q // 2)]
    L, m, R = q*q, len(colors), 4*q*q+1
    assert m == q*(q+1)//2
    lines = [frozenset(i for i, a in enumerate(row) if a == c)
             for row in colors[::q//2] for c in range(q)]
    assert all(len(line) == q for line in lines)
    assert len(set(lines)) == q*(q+1)
    assert all(len(a & b) <= 1 for i, a in enumerate(lines) for b in lines[:i])
    assert all(t*q-t*(t-1)//2 >= t*(q//2) for t in range(q+1))

    powers = [R ** i for i in range(2*m+3)]
    bumps = [[Q(powers[2*g+2], powers[2*a+1]+powers[2*g+2])
              - Q(powers[2*g], powers[2*a+1]+powers[2*g])
              for a in range(m+1)] for g in range(m)]
    for g, row in enumerate(bumps):
        for a, value in enumerate(row):
            if a == g:
                assert value == 1-Q(2,R+1)
            else:
                assert 0 <= value <= Q(1,R+1)

    rng = random.Random(982734+q)
    if q == 2:
        targets = list(itertools.product(range(q), repeat=m))
    else:
        targets = [[0]*m, [q-1]*m]
        targets += [[rng.randrange(q) for _ in range(m)] for _ in range(trials)]
    minimum = None
    positive_minimum = None
    checked = 0
    for target in targets:
        owner = [-1]*L

        def augment(g, seen):
            for i, color in enumerate(colors[g]):
                if color != target[g] or i in seen:
                    continue
                seen.add(i)
                if owner[i] < 0 or augment(owner[i], seen):
                    owner[i] = g
                    return True
            return False

        for g in range(m):
            assert augment(g, set())
        selected = [owner.index(g) for g in range(m)]
        assert len(set(selected)) == m
        levels = [g if g >= 0 else m for g in owner]
        assert all(levels[i] == g for g, i in enumerate(selected))
        for g in range(m):
            for bit in range(s):
                value = sum((1 if (colors[g][i] >> bit) & 1 else -1)
                            * bumps[g][levels[i]] for i in range(L))
                sign = 1 if (target[g] >> bit) & 1 else -1
                margin = sign*value
                assert margin >= 1-Q(L+1,R+1) > Q(1,2)
                # Expand every converted term independently, rather than
                # reusing the reciprocal-complement identity as a verifier.
                delta = Q(1, 8*L+1)
                positive_value = -L
                for i in range(L):
                    weight = 1 if (colors[g][i] >> bit) & 1 else -1
                    t = Q(powers[2*levels[i]+1])
                    for p, w in [(Q(powers[2*g+2]),weight),
                                 (Q(powers[2*g]),-weight)]:
                        if w == 1:
                            positive_value += p/(t+p) + delta/(1/t+1)
                        else:
                            positive_value += (1/p)/(1/t+1/p) + delta/(t+1)
                assert 0 < positive_value-value < Q(1,4)
                positive_margin = sign*positive_value
                assert positive_margin > Q(1,4)
                positive_minimum = (positive_margin if positive_minimum is None
                                    else min(positive_minimum,positive_margin))
                minimum = margin if minimum is None else min(minimum,margin)
                checked += 1
    return dict(q=q, field_modulus=modulus, parameters=2*L, tests=m*s,
                assignments_checked=len(targets), exact_test_evaluations=checked,
                selector_inequalities_checked=m*(m+1),
                positive_residue_parameters=4*L,
                positive_exact_test_evaluations=checked,
                minimum_positive_signed_margin=str(positive_minimum),
                minimum_signed_margin=str(minimum), status='PASS',
                main_target_proved=False)


if __name__ == '__main__':
    rows = [check(2, 0b11, 0), check(4, 0b111, 24), check(8, 0b1011, 8)]
    output = Path(__file__).with_name('reciprocal-matching-checks.json')
    output.write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps([{k:v for k,v in row.items() if not k.startswith('minimum_')}
                      for row in rows]))
