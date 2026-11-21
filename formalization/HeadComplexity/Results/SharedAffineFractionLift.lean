import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- A bounded rational feature that crosses denominator orientation at q = 1.
The shared affine correction in its finite lift is counted as one head. -/
noncomputable def orientationCrossingFeature (q t₁ t₀ : ℝ) : ℝ :=
  q * (t₁ - t₀) / ((q + 1) * (q * t₁ + t₀))

theorem orientationCrossingFeature_decomposition (q t₁ t₀ : ℝ)
    (hq : 0 < q) (hone : q ≠ 1) (hB : q * t₁ + t₀ ≠ 0) :
    orientationCrossingFeature q t₁ t₀ =
      2 * q / (q ^ 2 - 1) -
        q * (t₁ + t₀) / ((q - 1) * (q * t₁ + t₀)) := by
  have hp : q + 1 ≠ 0 := by positivity
  have hm : q - 1 ≠ 0 := sub_ne_zero.mpr hone
  have hs : q ^ 2 - 1 ≠ 0 := by
    have he : q ^ 2 - 1 = (q - 1) * (q + 1) := by ring
    rw [he]
    exact mul_ne_zero hm hp
  dsimp [orientationCrossingFeature]
  field_simp
  ring

theorem orientationCrossingFeature_at_one (t₁ t₀ : ℝ) :
    orientationCrossingFeature 1 t₁ t₀ = (t₁ - t₀) / (2 * (t₁ + t₀)) := by
  norm_num [orientationCrossingFeature]

theorem orientationCrossingFeature_error_identity (q t₁ t₀ : ℝ)
    (hq : 0 < q) (hP : t₁ + t₀ ≠ 0) (hB : q * t₁ + t₀ ≠ 0) :
    orientationCrossingFeature q t₁ t₀ - orientationCrossingFeature 1 t₁ t₀ =
      (q - 1) * (t₁ - t₀) * (t₀ - q * t₁) /
        (2 * (t₁ + t₀) * (q + 1) * (q * t₁ + t₀)) := by
  have hp : q + 1 ≠ 0 := by positivity
  rw [orientationCrossingFeature_at_one]
  dsimp [orientationCrossingFeature]
  field_simp
  ring

/-- The uniform error does not depend on the ratio of the shape coefficients.
Consequently a strict score at q = 1 has a finite ordinary-head lift. -/
theorem orientationCrossingFeature_error_le (q t₁ t₀ : ℝ)
    (hq : 0 < q) (h₁ : 0 ≤ t₁) (h₀ : 0 ≤ t₀) (hP : 0 < t₁ + t₀) :
    |orientationCrossingFeature q t₁ t₀ - orientationCrossingFeature 1 t₁ t₀| ≤
      |q - 1| / (2 * (q + 1)) := by
  have hB : 0 < q * t₁ + t₀ := by
    by_cases ht : t₁ = 0
    · simp only [ht, zero_add, mul_zero] at hP ⊢
      exact hP
    · exact add_pos_of_pos_of_nonneg (mul_pos hq (lt_of_le_of_ne h₁ (Ne.symm ht))) h₀
  have hL : |t₁ - t₀| ≤ t₁ + t₀ := by
    apply abs_le.mpr
    constructor <;> linarith
  have hM : |t₀ - q * t₁| ≤ q * t₁ + t₀ := by
    apply abs_le.mpr
    constructor <;> nlinarith
  rw [orientationCrossingFeature_error_identity q t₁ t₀ hq hP.ne' hB.ne']
  have hd : 0 < 2 * (t₁ + t₀) * (q + 1) * (q * t₁ + t₀) := by positivity
  simp only [abs_div, abs_mul, abs_of_pos hd]
  calc
    |q - 1| * |t₁ - t₀| * |t₀ - q * t₁| /
        (2 * (t₁ + t₀) * (q + 1) * (q * t₁ + t₀)) ≤
      |q - 1| * (t₁ + t₀) * (q * t₁ + t₀) /
        (2 * (t₁ + t₀) * (q + 1) * (q * t₁ + t₀)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hL (abs_nonneg _)) hM
          (abs_nonneg _) (by positivity)) hd.le
    _ = |q - 1| / (2 * (q + 1)) := by field_simp

end HeadComplexity
