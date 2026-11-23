#!/usr/bin/env python3
"""Emit finite rational certificates. Lean rechecks every displayed identity."""
from fractions import Fraction
from pathlib import Path
import json

BASE=Path(__file__).parent
ROOT=BASE.parent.parent
c=json.loads((BASE/'common-normal-maxima-certificate.json').read_text())
r=json.loads((BASE/'common-normal-maxima-rational-audit.json').read_text())
assert c['n']==4

def rat(x):
    v=Fraction(x)
    if v.denominator==1: return str(v.numerator)
    return f'({v.numerator} / {v.denominator})'

def vec(xs): return '!['+', '.join(map(rat,xs))+']'
def mat(rows): return '![\n  '+',\n  '.join(map(vec,rows))+']'

mu={k:u for k,u in zip(c['orbit_keys'],c['mu_numerators'])}
mus=[mu[min(x,(x&~3)|((x&1)<<1)|((x&2)>>1))] for x in range(16)]
pre='''import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-! Exact finite data for the common-normal local-maxima obstruction.
The differential and local-inverse argument is in the written proof.
No asymptotic head lower bound is asserted. -/
namespace HeadComplexity.CommonNormalMaxima
open scoped BigOperators

def bit (x : Fin 16) (i : ℕ) : ℚ := ((x.val / 2^i) % 2 : ℕ)
def y (x : Fin 16) (i : ℕ) : ℚ := if i = 0 then 1 else bit x (i-1)
def num (x : Fin 16) : ℚ := 4 + 2*bit x 0 + 3*bit x 1 + 8*bit x 2 + 4*bit x 3
def den (x : Fin 16) : ℚ := 1 + 5*bit x 0 + 6*bit x 1 + 7*bit x 2 + 5*bit x 3
def table (x : Fin 16) : ℚ := num x / den x
def swapped (x : Fin 16) : Fin 16 :=
  ⟨(x.val / 4 * 4 + (x.val % 2)*2 + (x.val / 2)%2) % 16, Nat.mod_lt _ (by decide)⟩
'''
pre+=f'\ndef muNumerators : Fin 16 → ℚ := {vec(mus)}\n'
pre+=f'def mu (x : Fin 16) : ℚ := muNumerators x / {c["mu_denominator"]}\n'
pre+='''
def jacobian : Matrix (Fin 16) (Fin 9) ℚ := fun x i ↦
  if i.val < 5 then y x i.val / den x
  else -table x * bit x (i.val-5) / den x

def halfHessian : Matrix (Fin 9) (Fin 9) ℚ := fun i j ↦ ∑ x : Fin 16,
  if i.val < 5 then
    if j.val < 5 then y x i.val * y x j.val / (den x)^2
    else (mu x - 2*table x) * y x i.val * bit x (j.val-5) / (den x)^2
  else
    if j.val < 5 then
      (mu x - 2*table x) * bit x (i.val-5) * y x j.val / (den x)^2
    else (3*(table x)^2 - 2*mu x*table x) *
      bit x (i.val-5) * bit x (j.val-5) / (den x)^2
'''
pre+=f'\ndef lower : Matrix (Fin 9) (Fin 9) ℚ := {mat(r["lower_factor"])}\n'
pre+=f'\ndef lowerInverse : Matrix (Fin 9) (Fin 9) ℚ := {mat(r["lower_inverse"])}\n'
pre+=f'\ndef pivots : Fin 9 → ℚ := {vec(r["least_squares_half_hessian_positive_pivots"])}\n'
pre+='''
theorem denominators_positive : ∀ x, 0 < den x := by decide +kernel
theorem functional_positive : ∀ x, 0 < mu x := by decide +kernel
theorem functional_swap_invariant : ∀ x, mu (swapped x) = mu x := by decide +kernel
theorem swap_involutive : ∀ x, swapped (swapped x) = x := by decide +kernel
theorem tables_distinct : table 5 ≠ table (swapped 5) := by decide +kernel

theorem stationarity : ∀ i : Fin 9,
    ∑ x : Fin 16, (mu x - table x) * jacobian x i = 0 := by decide +kernel

theorem hessian_factorization :
    halfHessian = lower * Matrix.diagonal pivots * lower.transpose := by decide +kernel

theorem lower_inverse_mul : lowerInverse * lower = 1 := by decide +kernel
theorem pivots_positive : ∀ i, 0 < pivots i := by decide +kernel

noncomputable def realHessian : Matrix (Fin 9) (Fin 9) ℝ := halfHessian.map (Rat.castHom ℝ)

theorem realHessian_posDef : realHessian.PosDef := by
  have hunit : IsUnit lower := (Matrix.isUnit_iff_isUnit_det lower).mpr
    (Matrix.isUnit_det_of_left_inverse lower_inverse_mul)
  have hunitR := hunit.map (Rat.castHom ℝ).mapMatrix
  have hp : (Matrix.diagonal (fun i ↦ (pivots i : ℝ))).PosDef :=
    Matrix.PosDef.diagonal fun i ↦ by exact_mod_cast pivots_positive i
  have h := (Matrix.IsUnit.posDef_star_right_conjugate_iff hunitR).mpr hp
  have heq : realHessian = lower.map (Rat.castHom ℝ) *
      Matrix.diagonal (fun i ↦ (pivots i : ℝ)) * (lower.map (Rat.castHom ℝ)).transpose := by
    ext i j
    have he := congrFun (congrFun hessian_factorization i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal,
      Matrix.map_apply, realHessian, Matrix.of_apply] at he ⊢
    change (halfHessian i j : ℝ) = ∑ x : Fin 9,
      (∑ x₁ : Fin 9, (lower i x₁ : ℝ) * if x₁ = x then (pivots x₁ : ℝ) else 0) *
      (lower j x : ℝ)
    have hc := congrArg (fun q : ℚ ↦ (q : ℝ)) he
    push_cast at hc
    simpa only [apply_ite, Rat.cast_zero] using hc
  simpa only [RingHom.mapMatrix_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, ← heq] using h

def pairFirst : Fin 4 → ℕ := ![0, 0, 0, 1]
def pairSecond : Fin 4 → ℕ := ![1, 2, 3, 2]
def vertex (v : ℕ) : Fin 16 := ⟨v % 16, Nat.mod_lt _ (by decide)⟩
def reconstruction : Matrix (Fin 4) (Fin 4) ℚ := fun r i ↦
  let j := pairFirst r
  let k := pairSecond r
  let t := table (vertex (2^j + 2^k))
  (if i.val = j then t - table (vertex (2^j)) else 0) +
  (if i.val = k then t - table (vertex (2^k)) else 0)

theorem reconstruction_det : reconstruction.det = -23/3432 := by decide +kernel

theorem radial_identity :
    (∑ x : Fin 16, mu x * table x) = ∑ x : Fin 16, (table x)^2 := by decide +kernel

end HeadComplexity.CommonNormalMaxima
'''
out=ROOT/'formalization/HeadComplexity/Atoms/CommonNormalMaxima.lean'
out.write_text(pre)
print(out, len(pre), 'bytes')
