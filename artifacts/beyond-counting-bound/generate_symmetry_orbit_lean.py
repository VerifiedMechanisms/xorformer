#!/usr/bin/env python3
"""Emit the six-point certificate for independent Lean kernel verification."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import json

BASE=Path(__file__).parent
ROOT=BASE.parent.parent
c=json.loads((BASE/'symmetry-orbit-maxima-certificate.json').read_text())
assert c['n']==6 and c['group_size']==3

def rat(x):
    v=F(x)
    return str(v.numerator) if v.denominator==1 else f'({v.numerator} / {v.denominator})'
def vec(xs):return '!['+', '.join(map(rat,xs))+']'
def mat(rows):return '![\n  '+',\n  '.join(map(vec,rows))+']'

text='''import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-! Six symmetry-related strict maxima: finite rational certificate.
The local differential argument is a written proof, not a declaration here. -/
namespace HeadComplexity.SymmetryOrbitMaxima
open scoped BigOperators

def bit (x : Fin 64) (i : ℕ) : ℚ := ((x.val / 2^i) % 2 : ℕ)
def y (x : Fin 64) (i : ℕ) : ℚ := if i = 0 then 1 else bit x (i-1)
def num (x : Fin 64) : ℚ :=
  -140 - 294*bit x 0 - 921*bit x 1 - 15*bit x 2 +
    1629*bit x 3 + 327*bit x 4 + 87*bit x 5
def den (x : Fin 64) : ℚ :=
  4 + 15*bit x 0 + 69*bit x 1 + bit x 2 +
    288*bit x 3 + 15*bit x 4 + 363*bit x 5
def table (x : Fin 64) : ℚ := num x / den x
'''
mus=[c['orbit_mu'][(x&7).bit_count()+4*(x>>3)] for x in range(64)]
text+='\ndef mu : Fin 64 → ℚ := '+vec(mus)+'\n'
perms=list(permutations(range(3)))
actions=[]
for p in perms:
    actions.append([(x&~7)+sum(((x>>p[i])&1)<<i for i in range(3)) for x in range(64)])
text+='\ndef action : Fin 6 → Fin 64 → Fin 64 := '+mat(actions)+'\n'
text+='''
def orbitTable (j : Fin 6) (x : Fin 64) : ℚ := table (action j x)
def jacobian : Matrix (Fin 64) (Fin 13) ℚ := fun x i ↦
  if i.val < 7 then y x i.val / den x
  else -table x * bit x (i.val-7) / den x
def halfHessian : Matrix (Fin 13) (Fin 13) ℚ := fun i j ↦ ∑ x : Fin 64,
  if i.val < 7 then
    if j.val < 7 then y x i.val * y x j.val / (den x)^2
    else (mu x - 2*table x) * y x i.val * bit x (j.val-7) / (den x)^2
  else
    if j.val < 7 then
      (mu x - 2*table x) * bit x (i.val-7) * y x j.val / (den x)^2
    else (3*(table x)^2 - 2*mu x*table x) *
      bit x (i.val-7) * bit x (j.val-7) / (den x)^2
'''
text+='\ndef lower : Matrix (Fin 13) (Fin 13) ℚ := '+mat(c['lower_factor'])+'\n'
text+='\ndef lowerInverse : Matrix (Fin 13) (Fin 13) ℚ := '+mat(c['lower_inverse'])+'\n'
text+='\ndef pivots : Fin 13 → ℚ := '+vec(c['positive_pivots'])+'\n'
text+='''
theorem denominators_positive : ∀ x, 0 < den x := by decide +kernel
theorem functional_invariant : ∀ j x, mu (action j x) = mu x := by decide +kernel
theorem action_bijective : ∀ j : Fin 6, Function.Bijective (action j) := by decide +kernel
theorem tables_distinct : ∀ i j : Fin 6, i ≠ j → ∃ x, orbitTable i x ≠ orbitTable j x := by
  decide +kernel
theorem orbit_equal_norm : ∀ j : Fin 6,
    (∑ x : Fin 64, (orbitTable j x)^2) = ∑ x : Fin 64, (table x)^2 := by
  decide +kernel
theorem stationarity : ∀ i : Fin 13,
    ∑ x : Fin 64, (mu x - table x) * jacobian x i = 0 := by decide +kernel
theorem hessian_factorization :
    halfHessian = lower * Matrix.diagonal pivots * lower.transpose := by decide +kernel
theorem lower_inverse_mul : lowerInverse * lower = 1 := by decide +kernel
theorem pivots_positive : ∀ i, 0 < pivots i := by decide +kernel

noncomputable def realHessian : Matrix (Fin 13) (Fin 13) ℝ := halfHessian.map (Rat.castHom ℝ)

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
    change (halfHessian i j : ℝ) = ∑ x : Fin 13,
      (∑ x₁ : Fin 13, (lower i x₁ : ℝ) * if x₁ = x then (pivots x₁ : ℝ) else 0) *
      (lower j x : ℝ)
    have hc := congrArg (fun q : ℚ ↦ (q : ℝ)) he
    push_cast at hc
    simpa only [apply_ite, Rat.cast_zero] using hc
  simpa only [RingHom.mapMatrix_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, ← heq] using h
'''
pairs=c['reconstruction_pairs']
text+='\ndef pairFirst : Fin 6 → ℕ := '+vec([p[0] for p in pairs])+'\n'
text+='\ndef pairSecond : Fin 6 → ℕ := '+vec([p[1] for p in pairs])+'\n'
text+='''
def vertex (v : ℕ) : Fin 64 := ⟨v % 64, Nat.mod_lt _ (by decide)⟩
def reconstruction : Matrix (Fin 6) (Fin 6) ℚ := fun r i ↦
  let j := pairFirst r
  let k := pairSecond r
  let t := table (vertex (2^j + 2^k))
  (if i.val = j then t - table (vertex (2^j)) else 0) +
  (if i.val = k then t - table (vertex (2^k)) else 0)
'''
text+='\ntheorem reconstruction_det : reconstruction.det = '+rat(c['reconstruction_determinant'])+' := by decide +kernel\n'
text+='''
theorem radial_identity :
    (∑ x : Fin 64, mu x * table x) = ∑ x : Fin 64, (table x)^2 := by decide +kernel
theorem positive_translation : ∀ x, 0 < mu x + 100 ∧ 0 < table x + 100 := by
  decide +kernel

end HeadComplexity.SymmetryOrbitMaxima
'''
out=ROOT/'formalization/HeadComplexity/Atoms/SymmetryOrbitMaxima.lean'
out.write_text(text)
print(out,len(text),'bytes')
