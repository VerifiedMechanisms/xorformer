"""Exact audit of a full-parameter reciprocal saddle grid.

All arithmetic uses fractions. This is an auxiliary geometric construction;
the sole head is positive on the entire cube and computes a constant function.
"""
from fractions import Fraction as F
import itertools
import json
from math import comb, prod
from pathlib import Path


def main():
    d, k = 5, 4
    q = (d + 1) // 2
    roots = [F(2) + F(j, q) for j in range(q)]
    exponent = d + 1 - 2 * q

    def polynomial(t):
        return prod(t-r for r in roots)

    residues = [polynomial(-F(j)) ** 2 * (-F(j)) ** exponent /
                prod(F(ell-j) for ell in range(d+1) if ell != j)
                for j in range(d+1)]
    backbone = [F(-5*k, 2), F(16*k), F(-27*k, 2)]
    terms = []
    for mask in range(1 << d):
        y = tuple((mask >> a) & 1 for a in range(d))
        weight = sum(y)
        for i in range(k):
            x = tuple(int(j == i) for j in range(k)) + y
            terms.append((x, residues[weight] / comb(d, weight)))
        if weight <= 2:
            terms.append(((0,) * k + y, backbone[weight] / comb(d, weight)))

    curvatures = []
    for r in roots:
        pp = prod(r-s for s in roots if s != r)
        alpha = 2 * pp**2 * r**exponent / prod(r+j for j in range(d+1))
        assert alpha > 0
        assert r*(d+r)*alpha < 2*(d+1)
        curvatures.append(alpha)

    checked = 0
    determinant_formulas = set()
    for choices in itertools.product(range(q), repeat=k):
        r = [roots[j] for j in choices]
        alpha = [curvatures[j] for j in choices]
        b = [v-1 for v in r] + [F(1)]*d
        n = k+d
        value = F(0)
        grad = [F(0)]*n
        hess = [[F(0) for _ in range(n)] for _ in range(n)]
        for x, coefficient in terms:
            den = 1 + sum(bi*xi for bi, xi in zip(b, x))
            assert den > 0
            value += coefficient/den
            support = [i for i, xi in enumerate(x) if xi]
            for i in support:
                grad[i] -= coefficient/den**2
                for j in support:
                    hess[i][j] += 2*coefficient/den**3
        assert value == 0
        assert all(v == 0 for v in grad)
        for i in range(k):
            for j in range(k):
                assert hess[i][j] == (alpha[i] if i == j else 0)
            for a in range(d):
                assert hess[i][k+a] == -r[i]*alpha[i]/d
        transverse = (2*k*(d+1)-sum(ri*(d+ri)*ai for ri, ai in zip(r, alpha)))/(d*(d-1))
        uniform = (-2*k+sum(ri**2*ai for ri, ai in zip(r, alpha)))/d
        assert transverse > 0
        for a in range(d):
            for c in range(d):
                expected = (uniform-transverse)/d + (transverse if a == c else 0)
                assert hess[k+a][k+c] == expected
        schur_uniform = uniform-sum(ri**2*ai for ri, ai in zip(r, alpha))/d
        assert schur_uniform == F(-2*k, d) < 0
        determinant = prod(alpha)*transverse**(d-1)*schur_uniform
        assert determinant < 0
        determinant_formulas.add(str(determinant))
        checked += 1
    record = dict(d=d, k=k, n=d+k, q=q, grid_points_checked=checked,
                  expected_grid_points=q**k, roots=list(map(str, roots)),
                  residues=list(map(str, residues)), backbone=list(map(str, backbone)),
                  all_values_zero=True, all_gradients_zero=True,
                  all_hessian_formulas_checked=True, hessian_negative_eigenvalues=1,
                  all_head_denominators_positive=True,
                  scope='one positive head; one Boolean sign pattern; no head lower bound')
    Path('artifacts/beyond-counting-bound/reciprocal-saddle-verification.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))


if __name__ == '__main__':
    main()
