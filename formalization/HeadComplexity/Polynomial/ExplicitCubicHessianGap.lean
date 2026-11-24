import HeadComplexity.Polynomial.ExplicitCubicQuantitativeBounds
import HeadComplexity.Polynomial.DeterminantPerturbation

set_option linter.style.header false

/-!
# A uniform quantitative Hessian gap for every oriented three-head cubic

This uses a concrete positive target minor and an elementary determinant
perturbation estimate. It has no spectral-theory or compactness assumptions.
-/

namespace HeadComplexity.ExplicitCubicHessianGap
noncomputable section
open scoped BigOperators Matrix
open GenericCubicHessianPullback ExplicitCubicQuantitativeBounds
open ExplicitCubicRawObstruction PureRoPEReplication

def entryGap : ℝ := minorGap / (8640 * 73 ^ 5)

/-- The conservative constant retained in the quantitative appendix. -/
def rawGapScale : ℝ := 4 * FiniteGridPole.explicitDelta ^ 6 * vandermondeBound ^ 2 /
  (12 ^ 11 * 10 ^ 10)

theorem rawGapScale_pos : 0 < rawGapScale := by
  have hd := FiniteGridPole.explicitDelta_pos
  have hv := vandermondeBound_pos
  unfold rawGapScale
  positivity

theorem rawGapScale_fourteen_lt_entryGap : rawGapScale / 14 < entryGap := by
  norm_num [rawGapScale, entryGap, minorGap, vandermondeBound, FiniteGridPole.explicitDelta]

theorem entryGap_pos : 0 < entryGap := by
  have hg := minorGap_pos
  unfold entryGap
  positivity

theorem entryGap_le_one : entryGap ≤ 1 := by
  norm_num [entryGap, minorGap, vandermondeBound, FiniteGridPole.explicitDelta]

theorem determinant_error_bound : 4320 * (73 : ℝ) ^ 5 * entryGap = minorGap / 2 := by
  unfold entryGap
  ring

def competitorMinor (N E : Fin 3 → Fin 14 → ℝ) (w : Fin 14 → ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  (polynomialHessian (cubic N E) w).submatrix firstSix firstSix

theorem competitorMinor_det_zero (N E : Fin 3 → Fin 14 → ℝ) (w : Fin 14 → ℝ)
    (h : Fin 3) (hp : linearValue (E h) w = 0) :
    (competitorMinor N E w).det = 0 := by
  have hr : (competitorMinor N E w).rank ≤ 5 :=
    (Matrix.rank_submatrix_le _ _ _).trans
      (ThreeHeadPoleHessian.hessian_rank_le_five_at_pole N E w h hp)
  by_contra hn
  have hu : IsUnit (competitorMinor N E w) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)
  have hf := Matrix.rank_of_isUnit _ hu
  simp only [Fintype.card_sum, Fintype.card_fin] at hf
  omega

theorem entry_gap_on_normalized_pole (N E : Fin 3 → Fin 14 → ℝ)
    (d : Fin 14 → ℝ) (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i = 1)
    (h : Fin 3) (hp : ∀ w, FiniteGridPole.value d w = 0 → linearValue (E h) w = 0) :
    ∃ w : Fin 14 → ℝ, (∀ i, |w i| ≤ 2) ∧ ∃ i j,
      entryGap < |polynomialHessian (cubic baseS baseB) w i j -
        polynomialHessian (cubic N E) w i j| := by
  obtain ⟨w, hdw, hw, hA, hdet⟩ := exists_pole_with_bounded_nonsingular_minor d hd hs
  refine ⟨w, hw, ?_⟩
  by_contra hn
  push Not at hn
  have hdiff (i j : Fin 3 ⊕ Fin 3) :
      |targetMinor w i j - competitorMinor N E w i j| ≤ entryGap :=
    hn (firstSix i) (firstSix j)
  have hB (i j : Fin 3 ⊕ Fin 3) : |competitorMinor N E w i j| ≤ 73 := by
    have ht : |competitorMinor N E w i j| ≤ |targetMinor w i j| +
        |targetMinor w i j - competitorMinor N E w i j| := by
      simpa [abs_sub_comm, add_comm] using abs_sub_le
        (competitorMinor N E w i j) (targetMinor w i j) 0
    linarith [hA i j, hdiff i j, entryGap_le_one]
  have hz := competitorMinor_det_zero N E w h (hp w hdw)
  have hb := DeterminantPerturbation.det_sub_det_le (by simp)
    (targetMinor w) (competitorMinor N E w) 73 entryGap (by norm_num) entryGap_pos.le
    (fun i j ↦ (hA i j).trans (by norm_num)) hB hdiff
  rw [hz, sub_zero, determinant_error_bound] at hb
  linarith [minorGap_pos]

theorem normalize_positive_direction (e : Fin 14 → ℝ) (he : ∀ i, 0 < e i) :
    ∃ d : Fin 14 → ℝ, (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
      ∀ w, FiniteGridPole.value d w = 0 → linearValue e w = 0 := by
  let s := ∑ i, e i
  have hs : 0 < s := by
    exact Finset.sum_pos (fun i _ ↦ he i) (by simp)
  refine ⟨fun i ↦ e i / s, fun i ↦ (div_pos (he i) hs).le, ?_, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self hs.ne'
  · intro w hw
    have hid : FiniteGridPole.value (fun i ↦ e i / s) w = linearValue e w / s := by
      simp only [FiniteGridPole.value, linearValue, div_mul_eq_mul_div, Finset.sum_div]
    rw [hid] at hw
    exact (div_eq_zero_iff).mp hw |>.resolve_right hs.ne'

/-- An oriented or zero denominator always admits a normalized nonnegative
direction with the same pole, including the entirely zero denominator. -/
theorem normalized_pole_of_oriented (e : Fin 14 → ℝ)
    (he : (∀ i, 0 < e i) ∨ (∀ i, e i < 0) ∨ e = 0) :
    ∃ d : Fin 14 → ℝ, (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
      ∀ w, FiniteGridPole.value d w = 0 → linearValue e w = 0 := by
  rcases he with hp | hn | hz
  · exact normalize_positive_direction e hp
  · obtain ⟨d, hd, hs, hzero⟩ := normalize_positive_direction (fun i ↦ -e i)
      (fun i ↦ neg_pos.mpr (hn i))
    refine ⟨d, hd, hs, ?_⟩
    intro w hw
    have h := hzero w hw
    simpa only [linearValue, neg_mul, Finset.sum_neg_distrib, neg_eq_zero] using h
  · refine ⟨fun _ ↦ 1 / 14, by intro i; norm_num, by norm_num, ?_⟩
    intro w _
    simp [hz, linearValue]

/-- Every oriented three-head cubic has a uniformly separated Hessian entry
somewhere in the coordinate cube of radius two. Numerators are unrestricted. -/
theorem oriented_cubic_hessian_gap (N E : Fin 3 → Fin 14 → ℝ)
    (hE : ∀ h, (∀ i, 0 < E h i) ∨ (∀ i, E h i < 0) ∨ E h = 0) :
    ∃ w : Fin 14 → ℝ, (∀ i, |w i| ≤ 2) ∧ ∃ i j,
      entryGap < |polynomialHessian (cubic baseS baseB) w i j -
        polynomialHessian (cubic N E) w i j| := by
  obtain ⟨d, hd, hs, hp⟩ := normalized_pole_of_oriented (E 0) (hE 0)
  exact entry_gap_on_normalized_pole N E d hd hs 0 hp

/-- The entrywise version with the exact constant used in the appendix.
An ordinary cubic-coefficient error at most `rawGapScale /2352` would give
Hessian-entry error at most `rawGapScale /14` via the factor168 estimate. -/
theorem oriented_cubic_hessian_gap_at_raw_scale (N E : Fin 3 → Fin 14 → ℝ)
    (hE : ∀ h, (∀ i, 0 < E h i) ∨ (∀ i, E h i < 0) ∨ E h = 0) :
    ∃ w : Fin 14 → ℝ, (∀ i, |w i| ≤ 2) ∧ ∃ i j,
      rawGapScale / 14 < |polynomialHessian (cubic baseS baseB) w i j -
        polynomialHessian (cubic N E) w i j| := by
  obtain ⟨w, hw, i, j, hij⟩ := oriented_cubic_hessian_gap N E hE
  exact ⟨w, hw, i, j, rawGapScale_fourteen_lt_entryGap.trans hij⟩

end
end HeadComplexity.ExplicitCubicHessianGap
