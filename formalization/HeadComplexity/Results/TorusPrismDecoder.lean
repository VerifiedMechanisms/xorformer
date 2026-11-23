import HeadComplexity.Atoms.PositiveAffineRatio

set_option linter.style.header false

/-!
# Positive rational interval decoders on one-hot products

These are analytic ingredients for the written local construction in
`artifacts/head-compression/torus-prism-decoder.tex`. They do not assert a
universal head bound on the full Boolean cube.
-/

namespace HeadComplexity

/-- A positive affine ratio decoding an initial segment of a fixed order. -/
noncomputable def rationalPrefixKernel (R : ℝ) (rank cutoff : ℕ) : ℝ :=
  R ^ (2 * cutoff + 1) / (1 + R ^ (2 * cutoff + 1) + R ^ (2 * rank))

private theorem prefix_fraction_close_to_one (t b R : ℝ)
    (ht : 0 < t) (hb : 0 ≤ b) (hR : 0 < R)
    (hsep : R * (1 + b) ≤ 2 * t) :
    |t / (1 + t + b) - 1| ≤ 2 / R := by
  have hden : 0 < 1 + t + b := by positivity
  have hle : t / (1 + t + b) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  have heq : -(t / (1 + t + b) - 1) = (1 + b) / (1 + t + b) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ hden hR).mpr
  have hnonneg : 0 ≤ 1 + b := by positivity
  nlinarith

private theorem prefix_fraction_close_to_zero (t b R : ℝ)
    (ht : 0 < t) (hb : 0 ≤ b) (hR : 0 < R)
    (hsep : R * t ≤ b) :
    |t / (1 + t + b)| ≤ 1 / R := by
  have hden : 0 < 1 + t + b := by positivity
  rw [abs_of_pos (div_pos ht hden)]
  apply (div_le_div_iff₀ hden hR).mpr
  nlinarith

/-- Prefix approximation uses strictly positive powers and has explicit error. -/
theorem rationalPrefixKernel_error (R : ℝ) (hR : 1 < R) (rank cutoff : ℕ) :
    |rationalPrefixKernel R rank cutoff - (if rank ≤ cutoff then 1 else 0)|
      ≤ 2 / R := by
  have hRpos : 0 < R := by linarith
  have hRone : 1 ≤ R := hR.le
  have ht : 0 < R ^ (2 * cutoff + 1) := pow_pos hRpos _
  have hb : 0 ≤ R ^ (2 * rank) := pow_nonneg hRpos.le _
  unfold rationalPrefixKernel
  split_ifs with hle
  · apply prefix_fraction_close_to_one _ _ _ ht hb hRpos
    have hp : R ^ (2 * rank) ≤ R ^ (2 * cutoff) :=
      pow_le_pow_right₀ hRone (by omega)
    have hone : 1 ≤ R ^ (2 * cutoff) := one_le_pow₀ hRone
    rw [pow_succ]
    have hmul := mul_le_mul_of_nonneg_left (add_le_add hone hp) hRpos.le
    nlinarith
  · simp only [sub_zero]
    have hsep : R * R ^ (2 * cutoff + 1) ≤ R ^ (2 * rank) := by
      calc
        R * R ^ (2 * cutoff + 1) = R ^ (2 * cutoff + 2) := by
          rw [show 2 * cutoff + 2 = (2 * cutoff + 1) + 1 by omega, pow_succ]
          ring
        _ ≤ R ^ (2 * rank) := pow_le_pow_right₀ hRone (by omega)
    exact (prefix_fraction_close_to_zero _ _ _ ht hb hRpos hsep).trans
      (by apply div_le_div_of_nonneg_right (by norm_num) hRpos.le)

/-- An interval is a difference of two ordered positive rational prefixes. -/
theorem rational_interval_difference (D upper lower : ℝ)
    (hD : 0 < D) (hlower : 0 ≤ lower) (horder : lower ≤ upper) :
    upper / (D + upper) - lower / (D + lower) =
      D * (upper - lower) / ((D + upper) * (D + lower)) := by
  have hu : 0 < D + upper := by linarith
  have hl : 0 < D + lower := by positivity
  field_simp
  ring

/-- Interval decoders have no negative leakage at any Boolean input. -/
theorem rational_interval_difference_nonneg (D upper lower : ℝ)
    (hD : 0 < D) (hlower : 0 ≤ lower) (horder : lower ≤ upper) :
    0 ≤ upper / (D + upper) - lower / (D + lower) := by
  rw [rational_interval_difference D upper lower hD hlower horder]
  apply div_nonneg
  · exact mul_nonneg hD.le (sub_nonneg.mpr horder)
  · apply mul_nonneg <;> linarith

/-- On the face with no row bits, each interval's leakage is small. -/
theorem rational_interval_difference_le_of_no_rows (upper lower : ℝ)
    (hlower : 0 ≤ lower) (horder : lower ≤ upper) :
    upper / (1 + upper) - lower / (1 + lower) ≤ 1 / (1 + lower) := by
  have hu : 0 < 1 + upper := by linarith
  have hl : 0 < 1 + lower := by positivity
  rw [rational_interval_difference 1 upper lower (by norm_num) hlower horder]
  apply (div_le_div_iff₀ (mul_pos hu hl) hl).mpr
  have hprod : (1 + lower) * (upper - lower) ≤ (1 + lower) * (1 + upper) :=
    mul_le_mul_of_nonneg_left (by linarith) hl.le
  nlinarith

/-- The complementary ratio decodes a suffix and supplies an exact row-axis zero. -/
noncomputable def rationalSuffixKernel (R : ℝ) (rank cutoff : ℕ) : ℝ :=
  R ^ (2 * rank) / (1 + R ^ (2 * rank) + R ^ (2 * cutoff + 1))

/-- Suffix approximation with the same explicit error. -/
theorem rationalSuffixKernel_error (R : ℝ) (hR : 1 < R) (rank cutoff : ℕ) :
    |rationalSuffixKernel R rank cutoff - (if cutoff < rank then 1 else 0)|
      ≤ 2 / R := by
  have hRpos : 0 < R := by linarith
  have hRone : 1 ≤ R := hR.le
  have ht : 0 < R ^ (2 * rank) := pow_pos hRpos _
  have hb : 0 ≤ R ^ (2 * cutoff + 1) := pow_nonneg hRpos.le _
  unfold rationalSuffixKernel
  split_ifs with hlt
  · apply prefix_fraction_close_to_one _ _ _ ht hb hRpos
    have hp : R ^ (2 * cutoff + 2) ≤ R ^ (2 * rank) :=
      pow_le_pow_right₀ hRone (by omega)
    have hone : 1 ≤ R ^ (2 * cutoff + 1) := one_le_pow₀ hRone
    have hmul := mul_le_mul_of_nonneg_left hone hRpos.le
    have hpow : R * R ^ (2 * cutoff + 1) = R ^ (2 * cutoff + 2) := by
      rw [show 2 * cutoff + 2 = (2 * cutoff + 1) + 1 by omega, pow_succ]
      ring
    rw [hpow] at hmul
    nlinarith
  · simp only [sub_zero]
    have hsep : R * R ^ (2 * rank) ≤ R ^ (2 * cutoff + 1) := by
      calc
        R * R ^ (2 * rank) = R ^ (2 * rank + 1) := by rw [pow_succ]; ring
        _ ≤ R ^ (2 * cutoff + 1) := pow_le_pow_right₀ hRone (by omega)
    exact (prefix_fraction_close_to_zero _ _ _ ht hb hRpos hsep).trans
      (by apply div_le_div_of_nonneg_right (by norm_num) hRpos.le)

/-- A two-ratio interval decoder whose numerator vanishes on the row axis. -/
noncomputable def gatedRationalInterval (p row upper lower : ℝ) : ℝ :=
  row / (p + row + lower) - row / (p + row + upper)

/-- Exact cancellation formula, with no restriction to one-hot inputs. -/
theorem gatedRationalInterval_eq (p row upper lower : ℝ)
    (hp : 0 < p) (hrow : 0 ≤ row) (hlower : 0 ≤ lower) (horder : lower ≤ upper) :
    gatedRationalInterval p row upper lower =
      row * (upper - lower) / ((p + row + lower) * (p + row + upper)) := by
  have hl : 0 < p + row + lower := by positivity
  have hu : 0 < p + row + upper := by linarith
  unfold gatedRationalInterval
  field_simp
  ring

/-- The two-head interval module has nonnegative leakage everywhere. -/
theorem gatedRationalInterval_nonneg (p row upper lower : ℝ)
    (hp : 0 < p) (hrow : 0 ≤ row) (hlower : 0 ≤ lower) (horder : lower ≤ upper) :
    0 ≤ gatedRationalInterval p row upper lower := by
  rw [gatedRationalInterval_eq p row upper lower hp hrow hlower horder]
  apply div_nonneg
  · exact mul_nonneg hrow (sub_nonneg.mpr horder)
  · apply mul_nonneg <;> linarith

@[simp] theorem gatedRationalInterval_zero_row (p upper lower : ℝ) :
    gatedRationalInterval p 0 upper lower = 0 := by
  simp [gatedRationalInterval]

@[simp] theorem gatedRationalInterval_equal_endpoints (p row endpoint : ℝ) :
    gatedRationalInterval p row endpoint endpoint = 0 := by
  simp [gatedRationalInterval]

end HeadComplexity
