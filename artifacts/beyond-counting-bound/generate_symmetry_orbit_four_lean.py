#!/usr/bin/env python3
"""Emit the twenty-four-point certificate for independent Lean kernel verification."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import json,sys
from verify_full_table_critical_points import inverse
sys.set_int_max_str_digits(0)

BASE=Path(__file__).parent
ROOT=BASE.parent.parent
c=json.loads((BASE/'symmetry-orbit-four-certificate.json').read_text())
assert c['n']==7 and c['group_size']==4

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

/-! Twenty-four symmetry-related strict maxima: finite rational certificate.
The local differential argument is a written proof, not a declaration here. -/
namespace HeadComplexity.SymmetryOrbitFour
open scoped BigOperators

def bit (x : Fin 128) (i : ℕ) : ℚ := ((x.val / 2^i) % 2 : ℕ)
def y (x : Fin 128) (i : ℕ) : ℚ := if i = 0 then 1 else bit x (i-1)
def num (x : Fin 128) : ℚ :=
  15 - 15*bit x 0 - 12*bit x 1 - 837*bit x 2 -
    48*bit x 3 - 66*bit x 4 + 14862*bit x 5 - 2642*bit x 6
def den (x : Fin 128) : ℚ :=
  1 + 11*bit x 0 + 7*bit x 1 + 375*bit x 2 +
    33*bit x 3 + 6*bit x 4 + 5240*bit x 5 + 266*bit x 6
def table (x : Fin 128) : ℚ := num x / den x
'''
mus=[c['orbit_mu'][(x&15).bit_count()+5*(x>>4)] for x in range(128)]
text+='\ndef mu : Fin 128 → ℚ := '+vec(mus)+'\n'
perms=list(permutations(range(4)))
actions=[]
for p in perms:
    actions.append([(x&~15)+sum(((x>>p[i])&1)<<i for i in range(4)) for x in range(128)])
text+='\ndef action : Fin 24 → Fin 128 → Fin 128 := '+mat(actions)+'\n'
inverses=[[row.index(x) for x in range(128)] for row in actions]
text+='\ndef inverseAction : Fin 24 → Fin 128 → Fin 128 := '+mat(inverses)+'\n'
text+='''
def orbitTable (j : Fin 24) (x : Fin 128) : ℚ := table (action j x)
def jacobian : Matrix (Fin 128) (Fin 15) ℚ := fun x i ↦
  if i.val < 8 then y x i.val / den x
  else -table x * bit x (i.val-8) / den x
def halfHessian : Matrix (Fin 15) (Fin 15) ℚ := fun i j ↦ ∑ x : Fin 128,
  if i.val < 8 then
    if j.val < 8 then y x i.val * y x j.val / (den x)^2
    else (mu x - 2*table x) * y x i.val * bit x (j.val-8) / (den x)^2
  else
    if j.val < 8 then
      (mu x - 2*table x) * bit x (i.val-8) * y x j.val / (den x)^2
    else (3*(table x)^2 - 2*mu x*table x) *
      bit x (i.val-8) * bit x (j.val-8) / (den x)^2
'''
text+='\ndef lower : Matrix (Fin 15) (Fin 15) ℚ := '+mat(c['lower_factor'])+'\n'
text+='\ndef lowerInverse : Matrix (Fin 15) (Fin 15) ℚ := '+mat(c['lower_inverse'])+'\n'
text+='\ndef pivots : Fin 15 → ℚ := '+vec(c['positive_pivots'])+'\n'
text+='''
theorem denominators_positive : ∀ x, 0 < den x := by decide +kernel
theorem functional_invariant : ∀ j x, mu (action j x) = mu x := by decide +kernel
theorem action_inverse : ∀ j x, inverseAction j (action j x) = x ∧
    action j (inverseAction j x) = x := by decide +kernel

theorem action_bijective : ∀ j : Fin 24, Function.Bijective (action j) := by
  intro j
  exact ⟨Function.LeftInverse.injective (fun x ↦ (action_inverse j x).1),
    Function.RightInverse.surjective (fun x ↦ (action_inverse j x).2)⟩
theorem tables_distinct : ∀ i j : Fin 24, i ≠ j → ∃ x, orbitTable i x ≠ orbitTable j x := by
  decide +kernel
theorem orbit_equal_norm : ∀ j : Fin 24,
    (∑ x : Fin 128, (orbitTable j x)^2) = ∑ x : Fin 128, (table x)^2 := by
  intro j
  exact Equiv.sum_comp (Equiv.ofBijective (action j) (action_bijective j))
    (fun x ↦ (table x)^2)
theorem stationarity : ∀ i : Fin 15,
    ∑ x : Fin 128, (mu x - table x) * jacobian x i = 0 := by decide +kernel
theorem hessian_factorization :
    halfHessian = lower * Matrix.diagonal pivots * lower.transpose := by decide +kernel
theorem lower_inverse_mul : lowerInverse * lower = 1 := by decide +kernel
theorem pivots_positive : ∀ i, 0 < pivots i := by decide +kernel

noncomputable def realHessian : Matrix (Fin 15) (Fin 15) ℝ := halfHessian.map (Rat.castHom ℝ)

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
    change (halfHessian i j : ℝ) = ∑ x : Fin 15,
      (∑ x₁ : Fin 15, (lower i x₁ : ℝ) * if x₁ = x then (pivots x₁ : ℝ) else 0) *
      (lower j x : ℝ)
    have hc := congrArg (fun q : ℚ ↦ (q : ℝ)) he
    push_cast at hc
    simpa only [apply_ite, Rat.cast_zero] using hc
  simpa only [RingHom.mapMatrix_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, ← heq] using h
'''
pairs=c['reconstruction_pairs']
text+='\ndef pairFirst : Fin 7 → ℕ := '+vec([p[0] for p in pairs])+'\n'
text+='\ndef pairSecond : Fin 7 → ℕ := '+vec([p[1] for p in pairs])+'\n'
text+='''
def vertex (v : ℕ) : Fin 128 := ⟨v % 128, Nat.mod_lt _ (by decide)⟩
def reconstruction : Matrix (Fin 7) (Fin 7) ℚ := fun r i ↦
  let j := pairFirst r
  let k := pairSecond r
  let t := table (vertex (2^j + 2^k))
  (if i.val = j then t - table (vertex (2^j)) else 0) +
  (if i.val = k then t - table (vertex (2^k)) else 0)
'''
a,b=list(map(F,c['a'])),list(map(F,c['b']))
def tab(v):
    bits=[(v>>i)&1 for i in range(7)]
    return (a[0]+sum(a[i+1]*bits[i] for i in range(7)))/(F(c['denominator_constant'])+sum(b[i]*bits[i] for i in range(7)))
reconstruction=[]
for i,j in pairs:
    row=[F(0)]*7;t=tab((1<<i)+(1<<j))
    row[i]=t-tab(1<<i);row[j]=t-tab(1<<j)
    reconstruction.append(row)
text+='\ndef reconstructionInverse : Matrix (Fin 7) (Fin 7) ℚ := '+mat(inverse(reconstruction))+'\n'
text+='\ntheorem reconstruction_inverse_mul : reconstructionInverse * reconstruction = 1 := by decide +kernel\n'
text+='\ntheorem reconstruction_det_ne_zero : reconstruction.det ≠ 0 := by\n  exact isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_left_inverse reconstruction_inverse_mul)\n' 
text+='''
theorem radial_identity :
    (∑ x : Fin 128, mu x * table x) = ∑ x : Fin 128, (table x)^2 := by decide +kernel
theorem positive_translation : ∀ x, 0 < mu x + 100 ∧ 0 < table x + 100 := by
  decide +kernel

end HeadComplexity.SymmetryOrbitFour
'''
out=ROOT/'formalization/HeadComplexity/Atoms/SymmetryOrbitFour.lean'
out.write_text(text)
print(out,len(text),'bytes')
