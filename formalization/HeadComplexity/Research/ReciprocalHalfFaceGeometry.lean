import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.style.header false

/-!
Elementary quantitative ingredients for the written opposite-two-head bounded
closure obstruction. This module does not claim the full compactness theorem.
-/

namespace HeadComplexity.ReciprocalHalfFaceGeometry

/-- When a positive affine ratio vanishes on one half face, its values on the
other half are close to a constant-numerator reciprocal profile. -/
theorem halfFace_reciprocal_error_le
    (A a B b : ℝ) (hB : 0 < B) (hb : 0 ≤ b) :
    |(A + a) / (B + b) - a / (B + b)| ≤ |A / B| := by
  have hBb : 0 < B + b := add_pos_of_pos_of_nonneg hB hb
  rw [add_div, add_sub_cancel_right, abs_div, abs_div,
    abs_of_pos hBb, abs_of_pos hB]
  exact div_le_div_of_nonneg_left (abs_nonneg A) hB (le_add_of_nonneg_right hb)

/-- A signed positive reciprocal profile is either nonnegative decreasing or
nonpositive increasing along an ordered chain. -/
def PositiveProfile (u₀ u₁ u₂ : ℝ) : Prop :=
  (0 ≤ u₂ ∧ u₂ ≤ u₁ ∧ u₁ ≤ u₀) ∨ (u₀ ≤ u₁ ∧ u₁ ≤ u₂ ∧ u₂ ≤ 0)

/-- The opposite denominator orientation reverses the two monotonicities. -/
def NegativeProfile (v₀ v₁ v₂ : ℝ) : Prop :=
  (0 ≤ v₀ ∧ v₀ ≤ v₁ ∧ v₁ ≤ v₂) ∨ (v₂ ≤ v₁ ∧ v₁ ≤ v₀ ∧ v₀ ≤ 0)

/-- A sum of opposite signed reciprocal profiles cannot have an isolated
middle spike. The hypotheses also hold for bounded pointwise limits. -/
theorem middle_abs_le_endpoints
    {u₀ u₁ u₂ v₀ v₁ v₂ : ℝ}
    (hu : PositiveProfile u₀ u₁ u₂) (hv : NegativeProfile v₀ v₁ v₂) :
    |u₁ + v₁| ≤ |u₀ + v₀| + |u₂ + v₂| := by
  have h₀p := le_abs_self (u₀ + v₀)
  have h₀n := neg_le_abs (u₀ + v₀)
  have h₂p := le_abs_self (u₂ + v₂)
  have h₂n := neg_le_abs (u₂ + v₂)
  have ha₀ := abs_nonneg (u₀ + v₀)
  have ha₂ := abs_nonneg (u₂ + v₂)
  rcases hu with ⟨hu₂, hu₂₁, hu₁₀⟩ | ⟨hu₀₁, hu₁₂, hu₂⟩ <;>
    rcases hv with ⟨hv₀, hv₀₁, hv₁₂⟩ | ⟨hv₂₁, hv₁₀, hv₀⟩ <;>
    apply abs_le.mpr <;> constructor <;> linarith

/-- In particular the exact profile `(0,1,0)` is impossible. -/
theorem not_isolated_middle_spike
    {u₀ u₁ u₂ v₀ v₁ v₂ : ℝ}
    (hu : PositiveProfile u₀ u₁ u₂) (hv : NegativeProfile v₀ v₁ v₂)
    (h₀ : u₀ + v₀ = 0) (h₂ : u₂ + v₂ = 0) : u₁ + v₁ = 0 := by
  have h := middle_abs_le_endpoints hu hv
  rw [h₀, h₂, abs_zero, zero_add] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

end HeadComplexity.ReciprocalHalfFaceGeometry
