#!/usr/bin/env python3
"""Exact finite audits of the full-table critical-point construction.

Checks limiting systems, not perturbed roots. The general existence proof
is the analytic argument in full-table-critical-points.md.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import hashlib
import json
import time


def inverse(a):
    n = len(a)
    b = [[F(x) for x in row] + [F(i == j) for j in range(n)]
         for i, row in enumerate(a)]
    for j in range(n):
        p = next(i for i in range(j, n) if b[i][j])
        b[j], b[p] = b[p], b[j]
        pivot = b[j][j]
        b[j] = [x / pivot for x in b[j]]
        for i in range(n):
            if i != j:
                q = b[i][j]
                b[i] = [x - q * y for x, y in zip(b[i], b[j])]
    assert all(b[i][j] == (i == j) for i in range(n) for j in range(n))
    return [row[n:] for row in b]


def determinant(a):
    b = [[F(x) for x in row] for row in a]
    n, det = len(a), F(1)
    for j in range(n):
        candidates = [i for i in range(j, n) if b[i][j]]
        if not candidates:
            return F(0)
        p = candidates[0]
        if p != j:
            b[j], b[p] = b[p], b[j]
            det = -det
        pivot = b[j][j]
        det *= pivot
        for i in range(j + 1, n):
            q = b[i][j] / pivot
            for l in range(j + 1, n):
                b[i][l] -= q * b[j][l]
    return det


def mv(a, x):
    return [sum((u * v for u, v in zip(row, x)), F(0)) for row in a]


def transpose(a):
    return list(map(list, zip(*a)))


def dot(x, y):
    return sum((a * b for a, b in zip(x, y)), F(0))


def gram_data(d, ell):
    k = len(ell)
    a = [1 << i for i in range(d)]
    J = [[F(0) for _ in ell] for _ in ell]
    dJ = [[[F(0) for _ in ell] for _ in ell] for _ in ell]
    remainder = [[F(0) for _ in ell] for _ in ell]
    for bits in product((0, 1), repeat=d + k):
        D = F(1 + sum(w * x for w, x in zip(a + list(ell), bits)))
        x = bits[d:]
        psi = [F((1 + ell[j]) * x[j], D) for j in range(k)]
        dpsi = [[F((i == j) * x[i], D) - psi[i] * x[j] / D
                 for i in range(k)] for j in range(k)]
        data_singleton = sum(bits) == 1 and sum(bits[:d]) == 0
        for i in range(k):
            for j in range(k):
                entry = psi[i] * psi[j]
                J[i][j] += entry
                if not data_singleton:
                    remainder[i][j] += entry
                for l in range(k):
                    dJ[l][i][j] += dpsi[l][i] * psi[j] + psi[i] * dpsi[l][j]
    assert all(J[i][j] - F(i == j) == remainder[i][j]
               for i in range(k) for j in range(k))
    return J, dJ


def scalar_data(d):
    N, q = 1 << d, (1 << (d - 1)) - 1
    coeff = [F(prod((-c - l) ** 2 for l in range(1, q + 1)),
               prod(v - c for v in range(1, N + 1) if v != c))
             for c in range(1, N + 1)]
    ans = {}
    for ell in range(1, q + 1):
        R = sum((c / (ell + j) for j, c in enumerate(coeff, 1)), F(0))
        Rp = -sum((c / (ell + j) ** 2 for j, c in enumerate(coeff, 1)), F(0))
        Rpp = 2 * sum((c / (ell + j) ** 3 for j, c in enumerate(coeff, 1)), F(0))
        C = F(prod((ell - l) ** 2 for l in range(1, q + 1) if l != ell),
              prod(ell + v for v in range(2, N + 1)))
        assert (1 + ell) * R == 0
        assert R + (1 + ell) * Rp == 0
        assert 2 * Rp + (1 + ell) * Rpp == 2 * C > 0
        fa = [sum((coeff[c - 1] * ((c - 1 >> i) & 1) / (c + ell)
                   for c in range(1, N + 1)), F(0)) for i in range(d)]
        va = [-(1 + ell) * sum((coeff[c - 1] * ((c - 1 >> i) & 1) / (c + ell) ** 2
                                for c in range(1, N + 1)), F(0)) for i in range(d)]
        ans[ell] = dict(C=C, fa=fa, va=va)
    return coeff, ans


def check(d, k):
    start = time.monotonic()
    N, q = 1 << d, (1 << (d - 1)) - 1
    a = [1 << i for i in range(d)]
    A = [1 + x for x in a]
    H = [[F(-(i == j)) + F(A[i], N) for j in range(d)] for i in range(d)]
    Hinv = [[F(-(i == j)) + F(A[i], d - 1) for j in range(d)] for i in range(d)]
    assert inverse(H) == Hinv
    coeff, scalar = scalar_data(d)
    grids = list(product(range(1, q + 1), repeat=k))
    data = []
    for ell in grids:
        J, dJ = gram_data(d, ell)
        data.append((ell, J, inverse(J), dJ))
    maxB = (k - 1) * (k + 1) * q ** k + 1
    for B in range(1, maxB + 1):
        eta = [F(B ** j) for j in range(k)]
        if all(all(mv(Jinv, eta)) and
               (1 + ell[0]) * mv(Jinv, eta)[0] + (1 + ell[1]) * mv(Jinv, eta)[1]
               for ell, J, Jinv, dJ in data):
            break
    else:
        raise AssertionError('finite polynomial-root avoidance failed')
    dets, centers, energies = [], [], []
    for ell, J, Jinv, dJ in data:
        r = mv(Jinv, eta)
        assert all(r) and all(eta)
        E = dot(eta, r)
        assert E > 0
        U = [A[i] * sum((eta[j] * scalar[ell[j]]['fa'][i] for j in range(k)), F(0))
             for i in range(d)]
        Va = [[eta[j] * x for x in scalar[ell[j]]['va']] for j in range(k)]
        z = mv(Hinv, U)
        diagonal = [-2 * eta[j] * scalar[ell[j]]['C'] * r[j] for j in range(k)]
        w = [dot(r, mv(dJ[j], r)) / (2 * diagonal[j]) for j in range(k)]
        zeta = mv(transpose(Hinv), mv(transpose(Va), r))
        assert mv(H, z) == U
        assert mv(transpose(H), zeta) == mv(transpose(Va), r)
        assert all(diagonal[j] * w[j] - dot(r, mv(dJ[j], r)) / 2 == 0
                   for j in range(k))
        # Reconstruction matrix uses unnormalized r. Positive normalization
        # multiplies all its entries by the same nonzero scalar.
        pair = [[F(0) for _ in range(d + k)] for _ in range(d + k)]
        row = 0
        for j in range(k):
            val = r[j] * (1 + ell[j]) / (1 + a[0] + ell[j])
            pair[row][0], pair[row][d + j] = val, val - r[j]
            row += 1
        for i in range(1, d):
            val = r[0] * (1 + ell[0]) / (1 + a[i] + ell[0])
            pair[row][i], pair[row][d] = val, val - r[0]
            row += 1
        val = (r[0] * (1 + ell[0]) + r[1] * (1 + ell[1])) / (1 + ell[0] + ell[1])
        pair[row][d], pair[row][d + 1] = val - r[0], val - r[1]
        assert determinant(pair) != 0
        det = determinant(H) ** 2 * prod(diagonal)
        assert det != 0
        dets.append(str(det))
        centers.append(dict(ell=ell, z=list(map(str, z)), w=list(map(str, w)),
                            zeta=list(map(str, zeta))))
        energies.append(str(E))
    report = dict(d=d, k=k, n=d+k, grid_count=len(grids),
                  theorem_branch_count=q ** k, common_integer_B=B,
                  avoidance_bound=maxB, first_limiting_determinant=dets[0],
                  first_limiting_energy=energies[0],
                  gram_singleton_decomposition=True,
                  all_reconstruction_determinants_nonzero=True,
                  all_limiting_systems_solved_exactly=True,
                  perturbed_roots_certified=False, elapsed_seconds=time.monotonic()-start)
    # Retain all small centers for an independent interval contraction audit.
    if d <= 3 and k <= 2:
        report['centers'] = centers
        report['partial_fraction_coefficients'] = list(map(str, coeff))
    return report


if __name__ == '__main__':
    results = []
    path = Path(__file__).with_name('full-table-critical-rational-audit.json')
    for d, k in [(2, 2), (3, 2), (3, 3), (4, 2), (4, 3), (5, 2)]:
        result = check(d, k)
        results.append(result)
        report = dict(status='IN PROGRESS', scope='exact limiting-system audits only',
                      cases=results,
                      verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
        path.write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps({k: v for k, v in result.items()
                          if k not in ('centers', 'partial_fraction_coefficients')}), flush=True)
    report['status'] = 'PASS'
    path.write_text(json.dumps(report, indent=2) + '\n')
