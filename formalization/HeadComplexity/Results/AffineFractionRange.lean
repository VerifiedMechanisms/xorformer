import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- An exact upper certificate for an affine fraction on a Boolean cube.
The hypothesis is the maximum of the affine difference `A - t * B`.
The numerator and denominator slopes need not have a common sign. -/
theorem affineFraction_le_of_coordinate_certificate
    {ι : Type*} [Fintype ι]
    (a₀ b₀ t : ℝ) (a b x : ι → ℝ)
    (hx : ∀ i, x i = 0 ∨ x i = 1)
    (hB : 0 < b₀ + ∑ i, b i * x i)
    (hcert : a₀ - t * b₀ + ∑ i, max 0 (a i - t * b i) ≤ 0) :
    (a₀ + ∑ i, a i * x i) / (b₀ + ∑ i, b i * x i) ≤ t := by
  have hterm (i : ι) :
      (a i - t * b i) * x i ≤ max 0 (a i - t * b i) := by
    rcases hx i with h | h
    · rw [h, mul_zero]
      exact le_max_left _ _
    · rw [h, mul_one]
      exact le_max_right _ _
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  have hid : (a₀ + ∑ i, a i * x i) - t * (b₀ + ∑ i, b i * x i) =
      a₀ - t * b₀ + ∑ i, (a i - t * b i) * x i := by
    simp only [sub_mul, Finset.sum_sub_distrib, mul_add, Finset.mul_sum, mul_assoc]
    ring
  apply (div_le_iff₀ hB).2
  linarith

/-- The corresponding exact lower certificate, obtained from the minimum
of the affine difference. This supplies a bound, not a universal head
representation theorem. -/
theorem affineFraction_ge_of_coordinate_certificate
    {ι : Type*} [Fintype ι]
    (a₀ b₀ t : ℝ) (a b x : ι → ℝ)
    (hx : ∀ i, x i = 0 ∨ x i = 1)
    (hB : 0 < b₀ + ∑ i, b i * x i)
    (hcert : 0 ≤ a₀ - t * b₀ + ∑ i, min 0 (a i - t * b i)) :
    t ≤ (a₀ + ∑ i, a i * x i) / (b₀ + ∑ i, b i * x i) := by
  have hterm (i : ι) :
      min 0 (a i - t * b i) ≤ (a i - t * b i) * x i := by
    rcases hx i with h | h
    · rw [h, mul_zero]
      exact min_le_left _ _
    · rw [h, mul_one]
      exact min_le_right _ _
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  have hid : (a₀ + ∑ i, a i * x i) - t * (b₀ + ∑ i, b i * x i) =
      a₀ - t * b₀ + ∑ i, (a i - t * b i) * x i := by
    simp only [sub_mul, Finset.sum_sub_distrib, mul_add, Finset.mul_sum, mul_assoc]
    ring
  apply (le_div_iff₀ hB).2
  linarith

/-- Exact error when two affine fractions are replaced by one fraction
with the sum denominator. Positive rescalings of either original head
may be chosen before applying the identity. -/
theorem affineFraction_pair_merge_error_identity (A B C D : ℝ)
    (hB : B ≠ 0) (hD : D ≠ 0) (hBD : B + D ≠ 0) :
    A / B + C / D - 2 * (A + C) / (B + D) =
      (D - B) / (B + D) * (A / B - C / D) := by
  field_simp
  ring

/-- A sufficient quantitative merging certificate. No claim is made
that an arbitrary large collection contains a pair meeting the bound. -/
theorem affineFraction_pair_merge_error_le (A B C D ρ R : ℝ)
    (hB : B ≠ 0) (hD : D ≠ 0) (hBD : B + D ≠ 0)
    (hρ : |(D - B) / (B + D)| ≤ ρ)
    (hR : |A / B - C / D| ≤ R) :
    |A / B + C / D - 2 * (A + C) / (B + D)| ≤ ρ * R := by
  rw [affineFraction_pair_merge_error_identity A B C D hB hD hBD, abs_mul]
  exact mul_le_mul hρ hR (abs_nonneg _) (le_trans (abs_nonneg _) hρ)

end HeadComplexity
