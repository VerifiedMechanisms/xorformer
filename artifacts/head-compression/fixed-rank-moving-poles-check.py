#!/usr/bin/env python3
"""Exact finite audit of four adaptive ordered pole shapes; no numerical solver."""
from fractions import Fraction as F
from itertools import product
from functools import reduce

SHAPES = {
    (1, 1): [98, 166, 237, 303, 368, 387, 486, 538],
    (-1, -1): [98, 180, 270, 332, 340, 419, 434, 441],
    (1, -1): [38, 73, 120, 150, 154, 201, 300, 393],
    (-1, 1): [25, 119, 206, 287, 375, 448, 474, 573],
}

def prod(xs):
    return reduce(lambda a, b: a * b, xs, F(1))

def sign(x):
    return (x > 0) - (x < 0)

T = [F(100 + j, 100) for j in range(4)]
checked = 0
for trends, shape in SHAPES.items():
    x = list(map(F, shape))
    dx = [prod(x[j] - x[k] for k in range(8) if k != j) for j in range(8)]
    lead = [sum((F((-1)**j, abs(dx[2*j+b])) for j in range(4)), F(0)) for b in range(2)]
    assert tuple(map(sign, lead)) == trends
    p = [v / 100000 for v in x]
    dp = [prod(p[j] - p[k] for k in range(8) if k != j) for j in range(8)]
    for word in product((-1, 1), repeat=4):
        roots = [(T[j] + T[j+1])/2 for j in range(3) if word[j] != word[j+1]]
        # N is negative at every pole; one root-mask reversal gives either phase.
        phase = -(-1)**len(roots)
        N = lambda t: phase * prod(t-r for r in roots)
        c = [abs(N(p[j])/dp[j]) for j in range(8)]
        assert min(c) > 0
        root_phase = -word[0]
        for j,t in enumerate(T):
            score = root_phase * sum(((-1)**h*c[h]/(t-p[h]) for h in range(8)),F(0))
            assert word[j] * score > 0
            assert score == root_phase * N(t)/prod(t-z for z in p)
        for b in range(2):
            vals = [sum(((-1)**j*c[2*j+b]/(t-p[2*j+b]) for j in range(4)),F(0)) for t in (T[0],T[-1])]
            assert sign(vals[0]-vals[1]) == trends[b]
        checked += 1
print(f'PASS: 4 exact leading-sign pairs and {checked} rational root/child systems')
