import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Boolean interpolation need not preserve stability

An exact auxiliary counterexample. This file makes no claim about the
worst-case head lower bound.
-/

namespace HeadComplexity.BooleanInterpolationStability

noncomputable def B₁ (z : Fin 3 → ℂ) : ℂ :=
  3 + z 0 + 27 * z 1 + 8 * z 2

noncomputable def B₂ (z : Fin 3 → ℂ) : ℂ :=
  2 + 15 * z 0 + 15 * z 1 + z 2

noncomputable def multilinear (z : Fin 3 → ℂ) : ℂ :=
  6 + 62 * z 0 + 504 * z 1 + 27 * z 2 +
    420 * z 0 * z 1 + 121 * z 0 * z 2 + 147 * z 1 * z 2

def UpperStable (f : (Fin 3 → ℂ) → ℂ) : Prop :=
  ∀ z, (∀ i, 0 < (z i).im) → f z ≠ 0

theorem denominator_product_upperStable : UpperStable (fun z => B₁ z * B₂ z) := by
  intro z hz
  have h₀ := hz 0
  have h₁ := hz 1
  have h₂ := hz 2
  have hb₁ : 0 < (B₁ z).im := by
    simp [B₁]
    linarith
  have hb₂ : 0 < (B₂ z).im := by
    simp [B₂]
    linarith
  apply mul_ne_zero
  · intro h
    rw [h] at hb₁
    simp at hb₁
  · intro h
    rw [h] at hb₂
    simp at hb₂

noncomputable def booleanPoint (x : Fin 3 → Bool) : Fin 3 → ℂ :=
  fun i => if x i then 1 else 0

theorem interpolation_agrees_on_boolean_cube (x : Fin 3 → Bool) :
    multilinear (booleanPoint x) = B₁ (booleanPoint x) * B₂ (booleanPoint x) := by
  unfold multilinear B₁ B₂ booleanPoint
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> norm_num

noncomputable def witness : Fin 3 → ℂ :=
  ![(-1518114267 / 1808988641 : ℂ) +
      (116143413 / 1808988641 : ℂ) * Complex.I,
    Complex.I, -1 + (1 / 100 : ℂ) * Complex.I]

theorem witness_in_upper_half_plane (i : Fin 3) : 0 < (witness i).im := by
  fin_cases i <;> norm_num [witness]

theorem witness_is_zero : multilinear witness = 0 := by
  apply Complex.ext <;> norm_num [multilinear, witness]

theorem multilinear_not_upperStable : ¬ UpperStable multilinear := by
  intro h
  exact h witness witness_in_upper_half_plane witness_is_zero

end HeadComplexity.BooleanInterpolationStability

#print axioms HeadComplexity.BooleanInterpolationStability.denominator_product_upperStable
#print axioms HeadComplexity.BooleanInterpolationStability.interpolation_agrees_on_boolean_cube
#print axioms HeadComplexity.BooleanInterpolationStability.multilinear_not_upperStable
