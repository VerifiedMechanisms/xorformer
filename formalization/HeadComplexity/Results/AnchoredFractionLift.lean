import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- A coordinate feature after subtracting the affine interpolation at the
anchor and its neighbors. Here `b` is the chosen slope, `p` is the sum of
the other slopes, and `v` is their active sum. -/
noncomputable def anchoredFractionFeature (t b p v : ℝ) : ℝ :=
  (1 + b + p) * t * v / (p * (1 + b * t + v))

/-- Each normalized feature is one affine term plus one affine fraction.
For a whole unit the affine terms share a single correction head. -/
theorem anchoredFractionFeature_decomposition (t b p v : ℝ)
    (ht : t = 0 ∨ t = 1) (hp : p ≠ 0) (hB : 1 + b * t + v ≠ 0) :
    anchoredFractionFeature t b p v =
      (1 + b + p) / p * t -
        ((1 + b + p) / p * (1 + b) * t) / (1 + b * t + v) := by
  rcases ht with rfl | rfl
  · simp [anchoredFractionFeature]
  · dsimp [anchoredFractionFeature]
    simp only [mul_one] at hB ⊢
    field_simp [hp, hB]
    ring

/-- Normalization is uniform even when the positive slopes have very
different magnitudes. This theorem asserts no universal sign capacity. -/
theorem anchoredFractionFeature_mem_Icc (t b p v : ℝ)
    (ht : t = 0 ∨ t = 1) (hb : 0 < b) (hp : 0 < p)
    (hv : 0 ≤ v) (hvp : v ≤ p) :
    anchoredFractionFeature t b p v ∈ Set.Icc (0 : ℝ) 1 := by
  rcases ht with rfl | rfl
  · simp [anchoredFractionFeature]
  · have hB : 0 < p * (1 + b * 1 + v) := by positivity
    constructor
    · dsimp [anchoredFractionFeature]
      positivity
    · dsimp [anchoredFractionFeature]
      apply (div_le_iff₀ hB).2
      nlinarith [mul_nonneg (show 0 ≤ 1 + b by positivity) (sub_nonneg.mpr hvp)]

/-- The upper anchor is normalized to one. -/
theorem anchoredFractionFeature_at_full (b p : ℝ)
    (hb : 0 < b) (hp : 0 < p) :
    anchoredFractionFeature 1 b p p = 1 := by
  have hB : 1 + b * 1 + p ≠ 0 := by positivity
  dsimp [anchoredFractionFeature]
  field_simp

/-- Recover the original coordinate fraction from its anchored feature. -/
theorem coordinateFraction_from_anchored (t b p v : ℝ)
    (ht : t = 0 ∨ t = 1) (hb : 0 < b) (hp : 0 < p)
    (hv : 0 ≤ v) :
    t / (1 + b * t + v) = t / (1 + b) -
      p / ((1 + b) * (1 + b + p)) * anchoredFractionFeature t b p v := by
  rcases ht with rfl | rfl
  · simp [anchoredFractionFeature]
  · have hB : 1 + b * 1 + v ≠ 0 := by positivity
    have hb' : 1 + b ≠ 0 := by positivity
    have hp' : 1 + b + p ≠ 0 := by positivity
    dsimp [anchoredFractionFeature]
    field_simp
    ring

end HeadComplexity
