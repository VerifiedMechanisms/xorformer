import Mathlib.Tactic

set_option linter.style.header false

/-! A pair of reciprocal functions isolates one geometrically spaced level.
These are ingredients for a free-query obstruction, not a head lower bound. -/

namespace HeadComplexity.ReciprocalLevelSelector

noncomputable def bump (R : ℝ) (g a : ℕ) : ℝ :=
  R ^ (2 * g + 2) / (R ^ (2 * a + 1) + R ^ (2 * g + 2)) -
    R ^ (2 * g) / (R ^ (2 * a + 1) + R ^ (2 * g))

theorem ratio_nonneg {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    0 ≤ p / (t + p) := le_of_lt (div_pos hp (add_pos ht hp))

theorem ratio_le_one {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    p / (t + p) ≤ 1 := by
  apply (div_le_iff₀ (add_pos ht hp)).mpr
  linarith

theorem ratio_le_small {R t p : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hp : 0 < p) (hgap : R * p ≤ t) :
    p / (t + p) ≤ 1 / (R + 1) := by
  apply (div_le_div_iff₀ (add_pos ht hp) (by linarith : 0 < R + 1)).mpr
  nlinarith

theorem ratio_ge_large {R t p : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hp : 0 < p) (hgap : R * t ≤ p) :
    R / (R + 1) ≤ p / (t + p) := by
  apply (div_le_div_iff₀ (by linarith : 0 < R + 1) (add_pos ht hp)).mpr
  nlinarith

theorem bump_nonneg {R : ℝ} (hR : 1 ≤ R) (g a : ℕ) :
    0 ≤ bump R g a := by
  have hpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have ht : 0 < R ^ (2 * a + 1) := pow_pos hpos _
  have hl : 0 < R ^ (2 * g) := pow_pos hpos _
  have hh : 0 < R ^ (2 * g + 2) := pow_pos hpos _
  have hpow : R ^ (2 * g) ≤ R ^ (2 * g + 2) :=
    pow_le_pow_right₀ hR (by omega)
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (add_pos ht hl) (add_pos ht hh)).mpr
  nlinarith

theorem bump_diagonal {R : ℝ} (hR : 0 < R) (g : ℕ) :
    bump R g g = 1 - 2 / (R + 1) := by
  have hz : R ^ (2 * g) ≠ 0 := ne_of_gt (pow_pos hR _)
  have hrz : R ≠ 0 := ne_of_gt hR
  have hsum : R + 1 ≠ 0 := by positivity
  simp only [bump, show 2 * g + 2 = (2 * g + 1) + 1 by omega, pow_succ]
  field_simp
  ring

theorem bump_off_diagonal {R : ℝ} (hR : 1 ≤ R) (g a : ℕ) (hne : a ≠ g) :
    bump R g a ≤ 1 / (R + 1) := by
  have hpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have ht : 0 < R ^ (2 * a + 1) := pow_pos hpos _
  have hl : 0 < R ^ (2 * g) := pow_pos hpos _
  have hh : 0 < R ^ (2 * g + 2) := pow_pos hpos _
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hgap : R * R ^ (2 * a + 1) ≤ R ^ (2 * g) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ hR (by omega)
    have h1 := ratio_le_one ht hh
    have h2 := ratio_ge_large hpos ht hl hgap
    have heq : 1 - R / (R + 1) = 1 / (R + 1) := by
      have : R + 1 ≠ 0 := by positivity
      field_simp
      ring
    dsimp [bump]
    linarith
  · have hgap : R * R ^ (2 * g + 2) ≤ R ^ (2 * a + 1) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ hR (by omega)
    have h1 := ratio_le_small hpos ht hh hgap
    have h2 := ratio_nonneg ht hl
    dsimp [bump]
    linarith

theorem bump_error {R : ℝ} (hR : 1 ≤ R) (g a : ℕ) :
    |bump R g a - if a = g then 1 else 0| ≤ 2 / (R + 1) := by
  by_cases heq : a = g
  · subst a
    rw [ite_eq_left rfl, bump_diagonal (lt_of_lt_of_le zero_lt_one hR)]
    have hp : 0 ≤ 2 / (R + 1) := by positivity
    rw [show 1 - 2 / (R + 1) - 1 = -(2 / (R + 1)) by ring, abs_neg,
      abs_of_nonneg hp]
  · rw [ite_eq_right heq, sub_zero, abs_of_nonneg (bump_nonneg hR g a)]
    have hu := bump_off_diagonal hR g a heq
    have hp : 0 ≤ 1 / (R + 1) := by positivity
    rw [show 2 / (R + 1) = 2 * (1 / (R + 1)) by ring]
    linarith

#print axioms bump_error

end HeadComplexity.ReciprocalLevelSelector
