#!/usr/bin/env python3
"""Directed dyadic interval contraction for nine full-table critical points.

Every interval operation rounds outwards using integer arithmetic. This is an
independent finite certificate of the displayed rescaled analytic equations,
not a Lean formalization of the general implicit-function theorem.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import time

from verify_full_table_critical_points import scalar_data, gram_data, inverse, mv

BITS = 1024
SCALE = 1 << BITS


def ceildiv(a, b):
    return -((-a) // b)


class I:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None, raw=False):
        if raw:
            self.lo, self.hi = lo, hi
        else:
            lo, hi = F(lo), F(lo if hi is None else hi)
            self.lo = lo.numerator * SCALE // lo.denominator
            self.hi = ceildiv(hi.numerator * SCALE, hi.denominator)
        assert self.lo <= self.hi

    @staticmethod
    def cast(x):
        return x if isinstance(x, I) else I(x)

    def __add__(self, other):
        other = I.cast(other)
        return I(self.lo + other.lo, self.hi + other.hi, raw=True)
    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo, raw=True)

    def __sub__(self, other):
        return self + -I.cast(other)

    def __rsub__(self, other):
        return I.cast(other) + -self

    def __mul__(self, other):
        other = I.cast(other)
        vals = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return I(min(vals) // SCALE, ceildiv(max(vals), SCALE), raw=True)
    __rmul__ = __mul__

    def reciprocal(self):
        assert self.lo > 0 or self.hi < 0, 'interval denominator meets zero'
        # Reciprocal is decreasing on either component of its domain.
        return I(SCALE * SCALE // self.hi,
                 ceildiv(SCALE * SCALE, self.lo), raw=True)

    def __truediv__(self, other):
        return self * I.cast(other).reciprocal()

    def __rtruediv__(self, other):
        return I.cast(other) * self.reciprocal()

    def __pow__(self, n):
        assert isinstance(n, int)
        if n < 0:
            return self.reciprocal() ** (-n)
        ans = I(1)
        for _ in range(n):
            ans = ans * self
        return ans

    def abs_upper(self):
        return max(abs(self.lo), abs(self.hi))


class AD:
    __slots__ = ('v', 'g')
    dim = 8

    def __init__(self, value, gradient=None):
        self.v = I.cast(value)
        self.g = [I(0) for _ in range(self.dim)] if gradient is None else gradient

    @staticmethod
    def cast(x):
        return x if isinstance(x, AD) else AD(x)

    def __add__(self, other):
        other = AD.cast(other)
        return AD(self.v + other.v, [a + b for a, b in zip(self.g, other.g)])
    __radd__ = __add__

    def __neg__(self):
        return AD(-self.v, [-x for x in self.g])

    def __sub__(self, other):
        return self + -AD.cast(other)

    def __rsub__(self, other):
        return AD.cast(other) + -self

    def __mul__(self, other):
        other = AD.cast(other)
        return AD(self.v * other.v,
                  [a * other.v + self.v * b for a, b in zip(self.g, other.g)])
    __rmul__ = __mul__

    def reciprocal(self):
        inv = self.v.reciprocal()
        return AD(inv, [-g * inv * inv for g in self.g])

    def __truediv__(self, other):
        return self * AD.cast(other).reciprocal()

    def __rtruediv__(self, other):
        return AD.cast(other) * self.reciprocal()

    def __pow__(self, n):
        if n < 0:
            return self.reciprocal() ** (-n)
        ans = AD(1)
        for _ in range(n):
            ans = ans * self
        return ans


def matvec(a, x):
    return [sum(u * v for u, v in zip(row, x)) for row in a]


def inner(x, y):
    return sum(a * b for a, b in zip(x, y))


def solve(a, rhs):
    n = len(a)
    m = [list(row) + [rhs[i]] for i, row in enumerate(a)]
    for j in range(n):
        candidates = [i for i in range(j, n) if m[i][j].v.lo > 0 or m[i][j].v.hi < 0]
        assert candidates, 'no certified nonzero elimination pivot'
        p = candidates[0]
        m[j], m[p] = m[p], m[j]
        pivot = m[j][j]
        m[j] = [x / pivot for x in m[j]]
        for i in range(n):
            if i != j:
                factor = m[i][j]
                m[i] = [x - factor * y for x, y in zip(m[i], m[j])]
    return [row[-1] for row in m]


def interval_determinant(a):
    m = [list(row) for row in a]
    ans = I(1)
    for j in range(len(m)):
        candidates = [i for i in range(j, len(m)) if m[i][j].lo > 0 or m[i][j].hi < 0]
        assert candidates, 'uncertified reconstruction pivot'
        p = candidates[0]
        if p != j:
            m[j], m[p] = m[p], m[j]
            ans = -ans
        pivot = m[j][j]
        ans *= pivot
        for i in range(j + 1, len(m)):
            factor = m[i][j] / pivot
            for l in range(j + 1, len(m)):
                m[i][l] -= factor * m[j][l]
    assert ans.lo > 0 or ans.hi < 0
    return ans


def system(d, k, ell, eta, coeff, delta, center, radius):
    n, dim = d + k, 2 * d + k
    AD.dim = dim
    xs = []
    for i, x in enumerate(center):
        gradient = [I(int(i == j)) for j in range(dim)]
        xs.append(AD(I(x - radius, x + radius), gradient))
    z, w, zeta = xs[:d], xs[d:d+k], xs[d+k:]
    a = [AD(1 << i) + delta ** 3 * z[i] for i in range(d)]
    t = [AD(ell[j]) + delta * w[j] for j in range(k)]
    b = a + t
    assert all(x.v.lo > 0 for x in b)
    total = 1 + sum(a)
    N = 1 << d
    h = [(1 + (1 << i)) - N * (1 + a[i]) / total for i in range(d)]
    Dh = [[-N * int(i == j) / total + N * (1 + a[i]) / total ** 2
           for j in range(d)] for i in range(d)]
    U = [AD(0) for _ in range(d)]
    V = [AD(0) for _ in range(k)]
    Ub = [[AD(0) for _ in range(n)] for _ in range(d)]
    Vb = [[AD(0) for _ in range(n)] for _ in range(k)]
    for j in range(k):
        for code in range(N):
            s = [(code >> i) & 1 for i in range(d)]
            D = 1 + sum(a[i] * s[i] for i in range(d)) + t[j]
            c = eta[j] * coeff[code]
            V[j] += c * (1 + t[j]) / D
            for l in range(n):
                yl = s[l] if l < d else int(l == d + j)
                Vb[j][l] += c * (int(l == d + j) / D - (1 + t[j]) * yl / D ** 2)
            for i in range(d):
                U[i] += c * (1 + a[i]) * s[i] / D
                for l in range(n):
                    yl = s[l] if l < d else int(l == d + j)
                    Ub[i][l] += c * s[i] * (int(l == i) / D - (1 + a[i]) * yl / D ** 2)
    G = [[AD(0) for _ in range(n)] for _ in range(n)]
    Gb = [[[AD(0) for _ in range(n)] for _ in range(n)] for _ in range(n)]
    for bits in product((0, 1), repeat=n):
        D = 1 + sum(b[i] * bits[i] for i in range(n))
        psi = [(1 + b[i]) * bits[i] / D for i in range(n)]
        dp = [[int(i == l) * bits[i] / D - psi[i] * bits[l] / D
               for i in range(n)] for l in range(n)]
        for i in range(n):
            for j in range(n):
                G[i][j] += psi[i] * psi[j]
                for l in range(n):
                    Gb[l][i][j] += dp[l][i] * psi[j] + psi[i] * dp[l][j]
    v = [eta[j] - V[j] / delta for j in range(k)]
    ra = [delta ** 3 * x for x in zeta]
    rt = solve([row[d:] for row in G[d:]],
               [v[j] - inner(G[d+j][:d], ra) for j in range(k)])
    r = ra + rt
    first = [h[i] / delta ** 3 - U[i] - delta * inner(G[i][d:], rt)
             - delta ** 4 * inner(G[i][:d], zeta) for i in range(d)]
    second = [-delta ** 2 * sum(Ub[i][d+j] * zeta[i] for i in range(d))
              - sum(Vb[i][d+j] * rt[i] for i in range(k)) / delta
              - inner(r, matvec(Gb[d+j], r)) / 2 for j in range(k)]
    third = [sum(Dh[j][i] * zeta[j] for j in range(d))
             - delta ** 3 * sum(Ub[j][i] * zeta[j] for j in range(d))
             - sum(Vb[j][i] * rt[j] for j in range(k))
             - delta * inner(r, matvec(Gb[i], r)) / 2 for i in range(d)]
    # Ratios are independent of the later positive norm rescaling of r.
    ratios = [(r[0] * (1 + a[0]) + rt[j] * (1 + t[j])) /
              ((1 + a[0] + t[j]) * rt[j]) for j in range(k)]
    assert all(x.v.lo > 0 or x.v.hi < 0 for x in rt)
    pairs = [(0,d+j) for j in range(k)] + [(i,d) for i in range(1,d)] + [(d,d+1)]
    reconstruction = [[I(0) for _ in range(n)] for _ in range(n)]
    for row,(i,j) in enumerate(pairs):
        value = (r[i]*(1+b[i]) + r[j]*(1+b[j])) / (1+b[i]+b[j])
        reconstruction[row][i] = (value-r[i]).v
        reconstruction[row][j] = (value-r[j]).v
    interval_determinant(reconstruction)
    # A separate curvature check. At a system zero, r=G^{-1}K, and
    # E_00 = 2 (K_0-G_0 r)^T G^{-1}(K_0-G_0 r)
    #        + 2 K_00^T r - r^T G_00 r.
    # Scale by delta^8 before evaluating to avoid enormous intermediate values.
    # The expression is enclosed on the whole box, so its positivity applies
    # in particular at the certified zero. Together with the negative fiber
    # Hessian this proves that the image critical point is a saddle.
    av, tv, bv, rv = [x.v for x in a], [x.v for x in t], [x.v for x in b], [x.v for x in r]
    Gv = [[x.v for x in row] for row in G]
    G0 = [[x.v for x in row] for row in Gb[0]]
    totalv = 1 + sum(av)
    h00 = [2*N*int(i == 0)/totalv**2 - 2*N*(1+av[i])/totalv**3 for i in range(d)]
    U00, V00 = [I(0) for _ in range(d)], [I(0) for _ in range(k)]
    for j in range(k):
        for code in range(N):
            s = [(code >> i) & 1 for i in range(d)]
            D = 1 + sum(av[i]*s[i] for i in range(d)) + tv[j]
            c = eta[j]*coeff[code]
            V00[j] += 2*c*(1+tv[j])*s[0]**2/D**3
            for i in range(d):
                U00[i] += c*s[i]*(-2*int(i == 0)*s[0]/D**2 + 2*(1+av[i])*s[0]**2/D**3)
    G00 = [[I(0) for _ in range(n)] for _ in range(n)]
    for bits in product((0, 1), repeat=n):
        D = 1 + sum(bv[i]*bits[i] for i in range(n))
        psi = [(1+bv[i])*bits[i]/D for i in range(n)]
        dp = [int(i == 0)*bits[i]/D - psi[i]*bits[0]/D for i in range(n)]
        ddp = [-2*int(i == 0)*bits[i]*bits[0]/D**2 + 2*psi[i]*bits[0]**2/D**2 for i in range(n)]
        for i in range(n):
            for j in range(n):
                G00[i][j] += ddp[i]*psi[j] + 2*dp[i]*dp[j] + psi[i]*ddp[j]
    scaled_first = [Dh[i][0].v-delta**3*Ub[i][0].v for i in range(d)] + [-delta**3*Vb[j][0].v for j in range(k)]
    scaled_second = [delta**4*h00[i]-delta**7*U00[i] for i in range(d)] + [-delta**7*V00[j] for j in range(k)]
    qvec = [u-delta**4*v for u,v in zip(scaled_first,matvec(G0,rv))]
    invq = solve([[AD(x) for x in row] for row in Gv], [AD(x) for x in qvec])
    curvature = 2*inner(qvec,[x.v for x in invq]) + 2*inner(scaled_second,rv) - delta**8*inner(rv,matvec(G00,rv))
    assert curvature.lo > 0, 'uncertified positive anchor curvature'
    return first + second + third, ratios, curvature


def check_interval_arithmetic():
    # Adversarial signed-endpoint checks, independent of the formula evaluator.
    vals = [F(-7, 3), F(-1, 7), F(0), F(2, 9), F(19, 4)]
    for a in vals:
        for b in vals:
            x, y = I(a), I(b)
            for got, exact in [(x + y, a+b), (x-y, a-b), (x*y, a*b)]:
                assert got.lo * exact.denominator <= exact.numerator * SCALE <= got.hi * exact.denominator
            if b:
                got, exact = x/y, a/b
                assert got.lo * exact.denominator <= exact.numerator * SCALE <= got.hi * exact.denominator


def run():
    check_interval_arithmetic()
    base = Path(__file__).parent
    data = json.loads((base/'full-table-critical-rational-audit.json').read_text())
    case = next(c for c in data['cases'] if c['d'] == 3 and c['k'] == 2)
    d, k, dim = 3, 2, 8
    coeff, scalar = scalar_data(d)
    eta = [F(case['common_integer_B'] ** j) for j in range(k)]
    delta, radius = F(1, 10**50), F(1, 10**20)
    N = 1 << d
    Hinv = [[F(-(i == j)) + F(1 + (1 << i), d-1) for j in range(d)] for i in range(d)]
    results, ratio_boxes = [], []
    for c in case['centers']:
        start = time.monotonic()
        ell = c['ell']
        center = list(map(F, c['z'] + c['w'] + c['zeta']))
        J, _ = gram_data(d, ell)
        r0 = mv(inverse(J), eta)
        diagonal = [-2 * eta[j] * scalar[ell[j]]['C'] * r0[j] for j in range(k)]
        A = [[F(0) for _ in range(dim)] for _ in range(dim)]
        for i in range(d):
            for j in range(d):
                A[i][j] = Hinv[i][j]
                A[d+k+i][d+k+j] = Hinv[j][i]
        for j in range(k):
            A[d+j][d+j] = 1 / diagonal[j]
        fbox, ratios, curvature = system(d,k,ell,eta,coeff,delta,center,radius)
        fcenter, _, _ = system(d,k,ell,eta,coeff,delta,center,F(0))
        contraction = 0
        for i in range(dim):
            row = []
            for j in range(dim):
                value = I(int(i == j)) - sum((I(A[i][l]) * fbox[l].g[j] for l in range(dim)), I(0))
                row.append(value.abs_upper())
            contraction = max(contraction, sum(row))
        displacement = max(sum((I(A[i][l]) * fcenter[l].v for l in range(dim)), I(0)).abs_upper()
                           for i in range(dim))
        assert contraction * 4 < SCALE, ('contraction', ell, F(contraction,SCALE))
        assert displacement * radius.denominator * 4 < radius.numerator * SCALE, ('center', ell)
        for j in range(k):
            target = F(1+ell[j], 2+ell[j])
            diff = ratios[j].v - target
            assert diff.abs_upper() * 1000 < SCALE
        ratio_boxes.append([r.v for r in ratios])
        result = dict(ell=ell, contraction_upper=str(F(contraction,SCALE)),
                      displacement_upper=str(F(displacement,SCALE)),
                      scaled_anchor_curvature_lower=str(F(curvature.lo,SCALE)),
                      scaled_anchor_curvature_upper=str(F(curvature.hi,SCALE)),
                      elapsed_seconds=time.monotonic()-start)
        results.append(result)
        print(json.dumps(dict(ell=ell, contraction_less_than_one_quarter=True,
                              displacement_less_than_radius_over_four=True,
                              image_reconstruction_invertible=True,
                              positive_anchor_curvature=True,
                              elapsed_seconds=result['elapsed_seconds'])), flush=True)
    for i, left in enumerate(ratio_boxes):
        for right in ratio_boxes[i+1:]:
            assert any(a.hi < b.lo or b.hi < a.lo for a,b in zip(left,right))
    report = dict(status='PASS', scope='nine rigorous interval contractions for the written rescaled system',
                  dimension=5, delta=str(delta), radius=str(radius), dyadic_precision=BITS,
                  all_jacobians_invertible=True, distinct_image_ratio_boxes=True,
                  all_image_reconstruction_matrices_invertible=True,
                  all_critical_points_are_saddles=True,
                  main_target_proved=False, results=results,
                  verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (base/'full-table-critical-interval-audit.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__':
    run()
