#!/usr/bin/env python3
"""Exact finite checks. This does not prove an asymptotic head lower bound."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import sympy as sp

BASE = Path(__file__).resolve().parent


def energy(b, v):
    return sum(bi * vi**2 for bi, vi in zip(b, v)) + sum(
        bi * vi for bi, vi in zip(b, v))**2


def add_vec(vs, n):
    return [sum(v[i] for v in vs) for i in range(n)]


counts = dict(representations=0, deformed_representations=0,
              sign_checks=0, spike_energy_identities=0,
              angular_projection_identities=0)


def audit(n, heads, bias):
    # A head is (constant numerator, linear numerator, normalized slopes,
    # complement orientation). All slopes are strictly positive.
    cube = list(product((0, 1), repeat=n))
    assert all(all(bi > 0 for bi in b) for _, _, b, _ in heads)
    score, gradients = [], [[] for _ in heads]
    for x in cube:
        value = bias
        for h, (a, u, b, flip) in enumerate(heads):
            z = [1-xi if flip else xi for xi in x]
            A = a + sum(ui*xi for ui, xi in zip(u, x))
            D = 1 + sum(bi*zi for bi, zi in zip(b, z))
            value += A/D
            gradients[h].append([-A*zi/D**2 for zi in z])
        assert value != 0
        score.append(value)
    labels = [1 if v > 0 else -1 for v in score]
    m = min(abs(v) for v in score)
    K = sum(energy(heads[h][2], g) for h, gs in enumerate(gradients) for g in gs)
    counts['representations'] += 1
    for eps in (F(1, 4), F(1, 16), F(1, 64)):
        t = eps*m/(2*(1+m))
        assert 0 < t <= eps*m/2 and t <= eps/2
        spike = [labels[0]*t/(t+sum(x)) for x in cube]
        table = [r+eps*S for r, S in zip(spike, score)]
        assert all(y*T > 0 for y, T in zip(labels, table))
        counts['sign_checks'] += len(cube)
        G = sum(T*T for T in table)
        assert G >= 1
        bs = [h[2] for h in heads] + [[1/t]*n]
        gs = [[[eps*gi for gi in g] for g in block] for block in gradients]
        spike_g = [[-labels[0]*t*t*xi/(t+sum(x))**2 for xi in x] for x in cube]
        gs.append(spike_g)
        for x, g in zip(cube, spike_g):
            k = sum(x)
            e = energy(bs[-1], g)
            assert e == t*t*k/(t+k)**3
            assert 0 <= e <= t*t
            counts['spike_energy_identities'] += 1
        V = F(0)
        for b, block in zip(bs, gs):
            raw = sum(energy(b, g) for g in block)
            mean = add_vec([[T*gi for gi in g] for T, g in zip(table, block)], n)
            angular = (G*raw-energy(b, mean))/G**2
            projected = sum(energy(b, [gi-T*mi/G for gi, mi in zip(g, mean)])
                            for T, g in zip(table, block))/G
            assert angular == projected
            assert 0 <= angular <= raw/G <= raw
            V += angular
            counts['angular_projection_identities'] += 1
        assert 0 <= V <= len(cube)*t*t+eps*eps*K <= eps*eps*(K+F(len(cube), 4))
        counts['deformed_representations'] += 1


# Every Boolean target in dimensions one through three, realized by a fixed
# Cauchy interpolation dictionary. Its construction is only a finite test.
for n in range(1, 4):
    cube = list(product((0, 1), repeat=n))
    addresses = [sum((2**i)*xi for i, xi in enumerate(x)) for x in cube]
    N = len(cube)
    C = sp.Matrix([[sp.Rational(1, j+1+v) for j in range(N)] for v in addresses])
    inverse = C.inv()
    for ys in product((-1, 1), repeat=N):
        residues = inverse*sp.Matrix(ys)
        heads = [(F(int(residues[j].p), int(residues[j].q))/(j+1), [F(0)]*n,
                  [F(2**i, j+1) for i in range(n)], False) for j in range(N)]
        audit(n, heads, F(0))

# Mixed coherent orientations, affine numerators, signed cancellation.
for n in range(2, 6):
    heads = []
    for h in range(4):
        heads.append((F((-1)**h*(h+2), h+1),
                      [F((-1)**(h+i)*(i+h+1), i+2) for i in range(n)],
                      [F(i+h+1, h+2) for i in range(n)], bool(h % 2)))
    audit(n, heads, F(1, 103))

report = {'status': 'PASS', **counts,
          'arithmetic': 'fractions.Fraction; exact Cauchy interpolation in sympy',
          'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'scope': 'Finite independent checks, not an asymptotic head-count theorem.',
          'main_target_proved': False, 'stronger_target_proved': False}
(BASE/'vanishing-energy-spike-rational-audit.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
