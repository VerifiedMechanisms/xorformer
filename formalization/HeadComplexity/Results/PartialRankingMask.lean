import Mathlib

set_option linter.style.header false

/-!
# A partial ranking mask and an obstruction to scalar triangular repair

The three-ratio identity cancels exactly when either of the two nonnegative
local statistics vanishes. It does not localize a whole cube cell: decreasing
the common positive baseline increases every positive comparison. Therefore a
single scalar multiple cannot repair one point while preserving an oppositely
labelled point with the same statistics and a smaller baseline.
-/

namespace HeadComplexity

/-- Three affine ratios whose cross difference cancels on either coordinate axis. -/
noncomputable def partialRankingMask (p u v : ℝ) : ℝ :=
  (u - v) / (p + u + v) - u / (p + u) + v / (p + v)

/-- Exact identity underlying the partial mask. -/
theorem partialRankingMask_eq (p u v : ℝ)
    (hp : 0 < p) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    partialRankingMask p u v =
      (u - v) * u * v / ((p + u + v) * (p + u) * (p + v)) := by
  unfold partialRankingMask
  have h1 : p + u + v ≠ 0 := by positivity
  have h2 : p + u ≠ 0 := by positivity
  have h3 : p + v ≠ 0 := by positivity
  field_simp
  ring

@[simp] theorem partialRankingMask_zero_left (p v : ℝ) :
    partialRankingMask p 0 v = 0 := by
  simp [partialRankingMask, neg_div]

@[simp] theorem partialRankingMask_zero_right (p u : ℝ) :
    partialRankingMask p u 0 = 0 := by
  simp [partialRankingMask]

/-- A strictly ordered pair gives a strict positive comparison. -/
theorem partialRankingMask_pos (p u v : ℝ)
    (hp : 0 < p) (hv : 0 < v) (huv : v < u) :
    0 < partialRankingMask p u v := by
  have hu : 0 < u := hv.trans huv
  rw [partialRankingMask_eq p u v hp hu.le hv.le]
  exact div_pos (mul_pos (mul_pos (sub_pos.mpr huv) hu) hv) (by positivity)

/-- With a fixed ordered positive pair, the mask strictly decreases with its baseline. -/
theorem partialRankingMask_strictAnti_parameter (p q u v : ℝ)
    (hp : 0 < p) (hpq : p < q) (hv : 0 < v) (huv : v < u) :
    partialRankingMask q u v < partialRankingMask p u v := by
  have hq : 0 < q := hp.trans hpq
  have hu : 0 < u := hv.trans huv
  rw [partialRankingMask_eq q u v hq hu.le hv.le,
    partialRankingMask_eq p u v hp hu.le hv.le]
  have hnum : 0 < (u - v) * u * v :=
    mul_pos (mul_pos (sub_pos.mpr huv) hu) hv
  have hDp : 0 < (p + u + v) * (p + u) * (p + v) := by positivity
  have hDq : 0 < (q + u + v) * (q + u) * (q + v) := by positivity
  have hden : (p + u + v) * (p + u) * (p + v) <
      (q + u + v) * (q + u) * (q + v) := by
    gcongr
  apply (div_lt_div_iff₀ hDq hDp).mpr
  exact mul_lt_mul_of_pos_left hden hnum

/-- A constant negative residual cannot be corrected at the smaller of two
positive scores while staying negative at the larger score. -/
theorem not_scalar_repair_of_ordered_positive_scores (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    ¬ ∃ k : ℝ, 0 < -1 + k * a ∧ -1 + k * b < 0 := by
  rintro ⟨k, hka, hkb⟩
  have hk : 0 < k := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hab hk.le
  linarith

/-- The partial mask cannot carry out this one-module cardinality repair step.
The point to preserve has the smaller baseline `p`, hence the larger score. -/
theorem not_partialRankingMask_scalar_repair (p q u v : ℝ)
    (hp : 0 < p) (hpq : p < q) (hv : 0 < v) (huv : v < u) :
    ¬ ∃ k : ℝ, 0 < -1 + k * partialRankingMask q u v ∧
      -1 + k * partialRankingMask p u v < 0 :=
  not_scalar_repair_of_ordered_positive_scores
    (partialRankingMask q u v) (partialRankingMask p u v)
    (partialRankingMask_pos q u v (hp.trans hpq) hv huv)
    (partialRankingMask_strictAnti_parameter p q u v hp hpq hv huv).le

/-- The corresponding cross difference with the opposite denominator orientation. -/
noncomputable def reversePartialRankingMask (p u v : ℝ) : ℝ :=
  (u - v) / (p - u - v) - u / (p - u) + v / (p - v)

/-- Opposite-orientation algebra remains valid whenever the baseline exceeds
the sum of the two nonnegative local statistics. -/
theorem reversePartialRankingMask_eq (p u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : u + v < p) :
    reversePartialRankingMask p u v =
      (u - v) * u * v / ((p - u - v) * (p - u) * (p - v)) := by
  unfold reversePartialRankingMask
  have h1 : p - u - v ≠ 0 := by linarith
  have h2 : p - u ≠ 0 := by linarith
  have h3 : p - v ≠ 0 := by linarith
  field_simp
  ring

@[simp] theorem reversePartialRankingMask_zero_left (p v : ℝ) :
    reversePartialRankingMask p 0 v = 0 := by
  simp [reversePartialRankingMask, neg_div]

@[simp] theorem reversePartialRankingMask_zero_right (p u : ℝ) :
    reversePartialRankingMask p u 0 = 0 := by
  simp [reversePartialRankingMask]

/-- The opposite-orientation mask also has a strict positive comparison sign. -/
theorem reversePartialRankingMask_pos (p u v : ℝ)
    (hv : 0 < v) (huv : v < u) (hp : u + v < p) :
    0 < reversePartialRankingMask p u v := by
  have hu : 0 < u := hv.trans huv
  have h1 : 0 < p - u - v := by linarith
  have h2 : 0 < p - u := by linarith
  have h3 : 0 < p - v := by linarith
  rw [reversePartialRankingMask_eq p u v hu.le hv.le hp]
  exact div_pos (mul_pos (mul_pos (sub_pos.mpr huv) hu) hv) (by positivity)

end HeadComplexity
