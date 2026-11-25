import HeadComplexity.Results.PureSourceLinearApproximation
import HeadComplexity.Results.PureThreeAveragedWitness

set_option linter.style.header false

/-!
# Two exact Boolean witnesses defeat every oriented common denominator shift

This concerns only the proposed representation with unchanged numerators and
denominators D_i+tL. It is not a lower bound for arbitrary vanilla heads.
-/

namespace HeadComplexity.PureThreeReplicatedGrid

open scoped BigOperators

def positiveShiftCounts : Fin 18 → ℕ :=
  ![0, 0, 9, 9, 9, 9, 0, 0, 9, 9, 4, 4, 0, 5, 9, 1, 4, 3]

def negativeShiftCounts : Fin 18 → ℕ :=
  ![0, 9, 9, 9, 0, 9, 0, 4, 9, 9, 0, 4, 0, 4, 6, 5, 0, 4]

noncomputable def shiftGridPoint (c : Fin 18 → ℕ) : Fin 18 → ℝ :=
  fun g ↦ 2 * (c g : ℝ) / 9 - 1

noncomputable def shiftedScore (t : ℝ) (q : Fin 18 → ℝ) : ℝ :=
  ∑ i, numerator i q / (denominator i q + t * linearScore q)

noncomputable def shiftedClassifier (t : ℝ) (x : Fin 162 → Bool) : Bool :=
  decide (0 < shiftedScore t (coordinate (m := 9) x))

/-- Exactly the two intervals with strict uniform denominator slopes and
positive denominators on the full cube for this common-shift ansatz. -/
def AdmissibleCommonShift (t : ℝ) : Prop :=
  (-(200 / 63) < t ∧ t < -(1 / 4)) ∨ (1 / 3 < t ∧ t < 200 / 63)

theorem exists_input_shiftGridPoint (c : Fin 18 → ℕ) (hc : ∀ g, c g ≤ 9) :
    ∃ x : Fin 162 → Bool, coordinate (m := 9) x = shiftGridPoint c := by
  have hg : RoPEGridLimit.InCenteredGrid 9 (shiftGridPoint c) := by
    intro g
    exact ⟨c g, hc g, rfl⟩
  obtain ⟨x, hx⟩ := RoPEGridLimit.exists_mean_eq_of_inCenteredGrid (by omega : 0 < 9)
    (shiftGridPoint c) hg
  refine ⟨fun i ↦ x ((finProdFinEquiv (m := 18) (n := 9)).symm i), ?_⟩
  rw [PureThreeAveragedWitness.coordinate_reindex, hx]

theorem inverse_ninth_shift (a t : ℝ) :
    (a / 9 + t * (1 / 9))⁻¹ = 9 * (a + t)⁻¹ := by
  rw [show a / 9 + t * (1 / 9) = (a + t) / 9 by ring, inv_div]
  rfl

theorem divide_ninth_shift (a b t : ℝ) :
    a / (b / 9 + t * (1 / 9)) = 9 * a / (b + t) := by
  rw [div_eq_mul_inv, inverse_ninth_shift]
  ring

theorem positiveShift_score_formula (t : ℝ) :
    shiftedScore t (shiftGridPoint positiveShiftCounts) =
      -42 / (1762 + t) - 22 / (1776 + t) + 66 / (1822 + t) := by
  norm_num [shiftedScore, shiftGridPoint, positiveShiftCounts, numerator, denominator,
    linearScore, linearWeight, u, d, Fin.sum_univ_succ]
  rw [show (592 / 3 : ℝ) = 1776 / 9 by norm_num,
    divide_ninth_shift, divide_ninth_shift, divide_ninth_shift]
  ring

theorem negativeShift_score_formula (t : ℝ) :
    shiftedScore t (shiftGridPoint negativeShiftCounts) =
      -54 / (1754 + t) + 14 / (1834 + t) + 42 / (1814 + t) := by
  norm_num [shiftedScore, shiftGridPoint, negativeShiftCounts, numerator, denominator,
    linearScore, linearWeight, u, d, Fin.sum_univ_succ]
  rw [divide_ninth_shift, divide_ninth_shift, divide_ninth_shift]
  ring

theorem positiveShift_source_negative : score (shiftGridPoint positiveShiftCounts) < 0 := by
  have he := positiveShift_score_formula 0
  norm_num [shiftedScore, score] at he
  unfold score
  rw [he]
  norm_num

theorem negativeShift_source_positive : 0 < score (shiftGridPoint negativeShiftCounts) := by
  have he := negativeShift_score_formula 0
  norm_num [shiftedScore, score] at he
  unfold score
  rw [he]
  norm_num

theorem positiveShift_wrong_label (t : ℝ) (ht : 1 / 3 < t) :
    0 < shiftedScore t (shiftGridPoint positiveShiftCounts) := by
  rw [positiveShift_score_formula]
  have h₁ : 0 < 1762 + t := by linarith
  have h₂ : 0 < 1776 + t := by linarith
  have h₃ : 0 < 1822 + t := by linarith
  have he : -42 / (1762 + t) - 22 / (1776 + t) + 66 / (1822 + t) =
      (-40 + 3544 * t + 2 * t ^ 2) / ((1762 + t) * (1776 + t) * (1822 + t)) := by
    field_simp
    ring
  rw [he]
  exact div_pos (by nlinarith [sq_nonneg t]) (mul_pos (mul_pos h₁ h₂) h₃)

theorem negativeShift_wrong_label (t : ℝ) (ht₁ : -(200 / 63) < t) (ht₂ : t < -(1 / 4)) :
    shiftedScore t (shiftGridPoint negativeShiftCounts) < 0 := by
  rw [negativeShift_score_formula]
  have h₁ : 0 < 1754 + t := by linarith
  have h₂ : 0 < 1834 + t := by linarith
  have h₃ : 0 < 1814 + t := by linarith
  have he : -54 / (1754 + t) + 14 / (1834 + t) + 42 / (1814 + t) =
      (392 + 3656 * t + 2 * t ^ 2) / ((1754 + t) * (1834 + t) * (1814 + t)) := by
    field_simp
    ring
  rw [he]
  have hs : t ^ 2 < 16 := by nlinarith
  exact div_neg_of_neg_of_pos (by nlinarith) (mul_pos (mul_pos h₁ h₂) h₃)

/-- This rules out only the common-shift ansatz, not general vanilla heads. -/
theorem common_shift_nine_disagrees (t : ℝ) (ht : AdmissibleCommonShift t) :
    ∃ x : Fin 162 → Bool, classifier 9 x ≠ shiftedClassifier t x := by
  rcases ht with hn | hp
  · obtain ⟨x, hx⟩ := exists_input_shiftGridPoint negativeShiftCounts
      (by intro g; fin_cases g <;> norm_num [negativeShiftCounts])
    refine ⟨x, ?_⟩
    have hs := negativeShift_source_positive
    have hw := negativeShift_wrong_label t hn.1 hn.2
    simp [classifier, shiftedClassifier, hx, hs, not_lt.mpr hw.le]
  · obtain ⟨x, hx⟩ := exists_input_shiftGridPoint positiveShiftCounts
      (by intro g; fin_cases g <;> norm_num [positiveShiftCounts])
    refine ⟨x, ?_⟩
    have hs := positiveShift_source_negative
    have hw := positiveShift_wrong_label t hp.1
    simp [classifier, shiftedClassifier, hx, not_lt.mpr hs.le, hw]

end HeadComplexity.PureThreeReplicatedGrid
