#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import sympy as sp

BASE = Path(__file__).resolve().parent
d = k = 3
n = d+k
q, m = 2**d-1, 2**d
B = [1, 2, 4]
edges = [(0, 1), (1, 2), (2, 0)]


def P(t):
    out = F(1)
    for r in range(1, q+1):
        out *= t-r
    return out


def prod_except(j, stop):
    out = F(1)
    for ell in range(1, stop+1):
        if ell != j:
            out *= ell-j
    return out


lam = [P(-j)/prod_except(j, m) for j in range(1, m+1)]
mu = [-P(-j)/(2*prod_except(j, q)) for j in range(1, q+1)]


def R(t):
    return sum(c/(t+j) for j, c in enumerate(lam, 1))


def Q(t):
    return sum(c/(t+j) for j, c in enumerate(mu, 1))


def Rp(t):
    return -sum(c/(t+j)**2 for j, c in enumerate(lam, 1))


def Qp(t):
    return -sum(c/(t+j)**2 for j, c in enumerate(mu, 1))


assert all(R(F(r)) == 0 and Q(F(r)) == F(1, 2) and Rp(F(r)) != 0
           for r in range(1, q+1))


def anchor_gradient(y):
    D = F(1+sum(b*xi for b, xi in zip(B, y)))
    return [1/D]+[F(xi)/D for xi in y]+[-F(xi)/D**2 for xi in y]


anchor_inputs = [(0, 0, 0)]
anchor_inputs += [tuple(int(i == j) for i in range(d)) for j in range(d)]
anchor_inputs += [tuple(int(i in edge) for i in range(d)) for edge in edges]
A = sp.Matrix([[sp.Rational(v.numerator, v.denominator) for v in anchor_gradient(y)]
               for y in anchor_inputs])
Ai = A.inv()
assert Ai*A == sp.eye(7)
detA = F(A.det())
assert detA != 0
tables = set()
checks = 0
literal_jacobians = 0


def literal_gradient(z, ts):
    den = F(1+sum(b*zi for b, zi in zip(B+list(ts), z)))
    num = F(1+sum(z[d:]))
    raw = [1/den]+[F(zi)/den for zi in z]+[-num*zi/den**2 for zi in z]
    order = [0]+list(range(1, d+1))+list(range(n+1, n+d+1))
    order += [index for i in range(k) for index in (1+d+i, n+1+d+i)]
    return [raw[index] for index in order]


for ts in product(range(1, q+1), repeat=k):
    table = tuple(F(1+sum(z[d:]), 1+sum(b*zi for b, zi in zip(B+list(ts), z)))
                  for z in product((0, 1), repeat=n))
    assert all(v > 0 for v in table)
    assert table not in tables
    tables.add(table)
    full_det = detA
    literal_rows = [literal_gradient(y+(0,)*k, ts) for y in anchor_inputs]
    assert sp.Matrix(literal_rows)[:, :7] == A
    assert all(v == 0 for row in literal_rows for v in row[7:])
    for i, t in enumerate(ts):
        vals = [F(2, t+j) for j in range(1, m+1)]
        assert sum(c*v for c, v in zip(lam, vals)) == 0
        assert sum(c*v for c, v in zip(mu, vals)) == 1
        J = [[R(F(t)), 2*Rp(F(t))], [Q(F(t)), 2*Qp(F(t))]]
        detJ = J[0][0]*J[1][1]-J[0][1]*J[1][0]
        assert detJ == -Rp(F(t)) != 0
        full_det *= detJ
        checks += 2
        selector = tuple(int(ell == i) for ell in range(k))
        gradients = [literal_gradient(tuple((j >> ell) & 1 for ell in range(d))+selector, ts)
                     for j in range(m)]
        pair_rows = [[sum(c*g[col] for c, g in zip(coeffs, gradients))
                      for col in range(2*n+1)] for coeffs in (lam, mu)]
        assert [row[7+2*i:9+2*i] for row in pair_rows] == J
        assert all(row[col] == 0 for row in pair_rows for col in range(7, 2*n+1)
                   if col not in (7+2*i, 8+2*i))
        literal_rows.extend(pair_rows)
    assert full_det != 0
    if ts in ((1, 1, 1), (1, 2, 3), (7, 7, 7)):
        assert F(sp.Matrix(literal_rows).det()) == full_det
    literal_jacobians += 1

result = {'status': 'PASS', 'dimension': n, 'isolated_regular_points': len(tables),
          'distinct_full_positive_tables': len(tables),
          'cube_value_positivity_checks': len(tables)*2**n,
          'selector_observation_checks': checks,
          'literal_full_observation_jacobians_checked': literal_jacobians,
          'literal_full_determinant_checks': 3,
          'anchor_jacobian_determinant': str(detA),
          'lambda': list(map(str, lam)), 'mu': list(map(str, mu)),
          'R_derivatives_at_roots': [str(Rp(F(r))) for r in range(1, q+1)],
          'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'scope': 'Exact finite replay and block Jacobian certificate. General family is a written theorem. No Boolean lower bound.',
          'main_target_proved': False, 'stronger_target_proved': False}
(BASE/'full-head-linear-fibers-rational-audit.json').write_text(json.dumps(result, indent=2)+'\n')


def rat(v):
    v = sp.Rational(v)
    return str(v.p) if v.q == 1 else '('+str(v.p)+' / '+str(v.q)+')'


def vec(v):
    return '!['+', '.join(v)+']'


def mat(a):
    return vec([vec([rat(v) for v in a.row(i)]) for i in range(a.rows)])


source = '''import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! General odd-cycle kernel algebra and a finite full-head fiber certificate.
The inverse-function theorem and general family are proved in the writeup. -/
namespace HeadComplexity.FullHeadLinearFibers

theorem pair_kernel_factor (a b v w : ℝ) :
    (a*v+b*w)*(1+a+b)-(a*(1+a)*v+b*(1+b)*w) = a*b*(v+w) := by ring

theorem odd_triangle_zero (v₀ v₁ v₂ : ℝ)
    (h₁ : v₀+v₁=0) (h₂ : v₁+v₂=0) (h₃ : v₂+v₀=0) :
    v₀=0 ∧ v₁=0 ∧ v₂=0 := by constructor; linarith; constructor <;> linarith

theorem triangle_star_zero {ι : Type*} [DecidableEq ι]
    (v : ι → ℝ) (i₀ i₁ i₂ : ι)
    (h₁ : v i₀+v i₁=0) (h₂ : v i₁+v i₂=0) (h₃ : v i₂+v i₀=0)
    (he : ∀ i, i ≠ i₀ → i ≠ i₁ → i ≠ i₂ → v i₀+v i=0) :
    ∀ i, v i=0 := by
  obtain ⟨hz₀, hz₁, hz₂⟩ := odd_triangle_zero _ _ _ h₁ h₂ h₃
  intro i
  by_cases h : i=i₀
  · simpa [h] using hz₀
  by_cases h' : i=i₁
  · simpa [h'] using hz₁
  by_cases h'' : i=i₂
  · simpa [h''] using hz₂
  have ht := he i h h' h''
  linarith

theorem selector_det (r s : ℝ) :
    Matrix.det (!![0, 2*r; (1/2:ℝ), 2*s]) = -r := by
  norm_num [Matrix.det_fin_two] <;> ring

'''
source += 'def residueR : Fin 8 → ℚ := '+vec([rat(v) for v in lam])+'\n'
source += 'def residueQ : Fin 7 → ℚ := '+vec([rat(v) for v in mu])+'\n'
source += 'def responseR (t : ℚ) := ∑ j, residueR j / (t+j.val+1)\n'
source += 'def responseQ (t : ℚ) := ∑ j, residueQ j / (t+j.val+1)\n'
source += 'def derivativeR (t : ℚ) := -∑ j, residueR j / (t+j.val+1)^2\n'
source += 'theorem rational_roots : ∀ r : Fin 7, responseR (r.val+1)=0 ∧ responseQ (r.val+1)=1/2 := by decide +kernel\n'
source += 'theorem rational_simple : ∀ r : Fin 7, derivativeR (r.val+1) ≠ 0 := by decide +kernel\n'
source += 'def anchorJacobian : Matrix (Fin 7) (Fin 7) ℚ := '+mat(A)+'\n'
source += 'def anchorInverse : Matrix (Fin 7) (Fin 7) ℚ := '+mat(Ai)+'\n'
source += 'theorem anchor_inverse_mul : anchorInverse*anchorJacobian=1 := by decide +kernel\n'
source += '''
theorem table_positive {d k : ℕ} (B : Fin d → ℝ) (t : Fin k → ℝ)
    (hB : ∀ j, 0 < B j) (ht : ∀ i, 0 < t i)
    (y : Fin d → ℝ) (x : Fin k → ℝ)
    (hy : ∀ j, 0 ≤ y j) (hx : ∀ i, 0 ≤ x i) :
    0 < (1+∑ i, x i)/(1+∑ j, B j*y j+∑ i, t i*x i) := by
  have h₁ : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ ↦ hx i
  have h₂ : 0 ≤ ∑ j, B j*y j := Finset.sum_nonneg fun j _ ↦ mul_nonneg (hB j).le (hy j)
  have h₃ : 0 ≤ ∑ i, t i*x i := Finset.sum_nonneg fun i _ ↦ mul_nonneg (ht i).le (hx i)
  exact div_pos (by linarith) (by linarith)

end HeadComplexity.FullHeadLinearFibers
'''
Path('formalization/HeadComplexity/Atoms/FullHeadLinearFibers.lean').write_text(source)
print(json.dumps({key: result[key] for key in ('status', 'isolated_regular_points',
      'distinct_full_positive_tables', 'cube_value_positivity_checks',
      'anchor_jacobian_determinant')}, indent=2))
