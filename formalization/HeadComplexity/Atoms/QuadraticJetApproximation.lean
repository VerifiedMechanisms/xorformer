import Mathlib.Tactic

set_option linter.style.header false

/-! Exact finite-difference identities used in a linear-cost compiler for
quadratic reciprocal jets. These are auxiliary identities, not the requested
asymptotic head-complexity lower bound. -/
namespace HeadComplexity.QuadraticJetApproximation

noncomputable def secondDifference (B t L : ℝ) : ℝ :=
  (1 / (B - t * L) + 1 / (B + t * L) - 2 / B) / (2 * t ^ 2)

theorem secondDifference_eq (B t L : ℝ) (hB : B ≠ 0) (ht : t ≠ 0)
    (hminus : B - t * L ≠ 0) (hplus : B + t * L ≠ 0) :
    secondDifference B t L = L ^ 2 / (B * (B ^ 2 - t ^ 2 * L ^ 2)) := by
  have hfactor : B ^ 2 - t ^ 2 * L ^ 2 = (B - t * L) * (B + t * L) := by ring
  have hquad : B ^ 2 - t ^ 2 * L ^ 2 ≠ 0 := by rw [hfactor]; exact mul_ne_zero hminus hplus
  unfold secondDifference
  field_simp [hB, ht, hminus, hplus, hquad]
  ring

theorem error_identity (B t L : ℝ) (hB : B ≠ 0) (ht : t ≠ 0)
    (hminus : B - t * L ≠ 0) (hplus : B + t * L ≠ 0) :
    secondDifference B t L - L ^ 2 / B ^ 3 =
      t ^ 2 * L ^ 4 / (B ^ 3 * (B ^ 2 - t ^ 2 * L ^ 2)) := by
  rw [secondDifference_eq B t L hB ht hminus hplus]
  have hfactor : B ^ 2 - t ^ 2 * L ^ 2 = (B - t * L) * (B + t * L) := by ring
  have hnormalized : -(L ^ 2 * t ^ 2) + B ^ 2 ≠ 0 := by
    convert mul_ne_zero hminus hplus using 1
    ring
  rw [hfactor]
  field_simp [hB, hminus, hplus]
  ring_nf
  field_simp [hnormalized]
  ring

theorem perturbations_positive (b t a : ℝ) (hb : 0 < b) (hsmall : 2 * |t * a| ≤ b) :
    0 < b - t * a ∧ 0 < b + t * a := by
  have hlo := neg_abs_le (t * a)
  have hhi := le_abs_self (t * a)
  constructor <;> linarith

theorem error_bound (B t L : ℝ) (hB : 0 < B) (ht : t ≠ 0)
    (hsmall : 2 * |t * L| ≤ B) :
    |secondDifference B t L - L ^ 2 / B ^ 3| ≤ 2 * t ^ 2 * L ^ 4 / B ^ 5 := by
  have hp := perturbations_positive B t L hB hsmall
  rw [error_identity B t L hB.ne' ht hp.1.ne' hp.2.ne']
  have hsquare : 2 * t ^ 2 * L ^ 2 ≤ B ^ 2 := by
    have ha : 0 ≤ |t * L| := abs_nonneg _
    have habs : |t * L| ^ 2 = t ^ 2 * L ^ 2 := by rw [sq_abs]; ring
    nlinarith
  have hquad : 0 < B ^ 2 - t ^ 2 * L ^ 2 := by nlinarith [sq_pos_of_pos hB]
  have hnum : 0 ≤ t ^ 2 * L ^ 4 := by positivity
  have hden : 0 < B ^ 3 * (B ^ 2 - t ^ 2 * L ^ 2) := by positivity
  rw [abs_of_nonneg (div_nonneg hnum hden.le)]
  have hhalf : 0 < B ^ 5 / 2 := by positivity
  have hdenle : B ^ 5 / 2 ≤ B ^ 3 * (B ^ 2 - t ^ 2 * L ^ 2) := by
    have hscaled := mul_nonneg (pow_nonneg hB.le 3) (sub_nonneg.mpr hsquare)
    nlinarith
  calc
    _ ≤ (t ^ 2 * L ^ 4) / (B ^ 5 / 2) := div_le_div_of_nonneg_left hnum hhalf hdenle
    _ = _ := by ring

/-- A downward bias handles the zeros of the target as well as its negative
values, once its positive values have a finite margin. -/
theorem sign_preserved (F G γ : ℝ) (hγ : 0 < γ) (hgap : 0 < F → γ ≤ F)
    (herror : |G - F| < γ / 4) : 0 < G - γ / 2 ↔ 0 < F := by
  have hboth := abs_lt.mp herror
  constructor
  · intro hG
    by_contra! hF
    linarith [hboth.2]
  · intro hF
    have hmargin := hgap hF
    linarith [hboth.1]

end HeadComplexity.QuadraticJetApproximation
