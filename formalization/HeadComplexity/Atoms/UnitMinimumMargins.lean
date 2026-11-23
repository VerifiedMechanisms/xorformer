import HeadComplexity.Atoms.UnitMinimumInverseBounds

set_option linter.style.header false

namespace HeadComplexity.UnitMinimumAnalytic

open scoped BigOperators
open Metric Set
open UnitMinimumCenter (indices labels gamma)

noncomputable def fullLabel (v : ℕ) : ℝ :=
  if -(gamma : ℝ) / 2 ≤ (UnitMinimumCenter.score v : ℝ) then 1 else -1

noncomputable def candidateScore (v : ℕ) (z : Space) : ℝ := 1 + (2 / (gamma : ℝ)) * T v z

theorem gamma_real_pos : (0 : ℝ) < gamma := by norm_num [gamma]

theorem active_labels_values (r : Fin 108) : labels r = 1 ∨ labels r = -1 := by
  fin_cases r <;> decide +kernel

theorem indices_bound (r : Fin 108) : indices r < 2^18 := by
  fin_cases r <;> decide +kernel

theorem active_center_residual_real (r : Fin 108) :
    |(UnitMinimumCenter.score (indices r) : ℝ) +
      if labels r < 0 then (gamma : ℝ) else 0| < 1 / 10^60 := by
  have hc : ((|UnitMinimumCenter.score (indices r) +
      if labels r < 0 then gamma else 0| : ℚ) : ℝ) < ((1 / 10^60 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr (UnitMinimumCenter.active_residual r)
  split_ifs at hc ⊢ <;> simpa only [Rat.cast_abs, Rat.cast_add, Rat.cast_zero,
    Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hc

theorem fullLabel_active (r : Fin 108) : fullLabel (indices r) = (labels r : ℝ) := by
  have hh := active_center_residual_real r
  have hg : (2 / 10^60 : ℝ) < gamma := by norm_num [gamma]
  rcases active_labels_values r with hy | hy
  · rw [hy] at hh ⊢
    norm_num at hh ⊢
    have hb := (abs_lt.mp hh).1
    have hc : -(gamma : ℝ) / 2 ≤ (UnitMinimumCenter.score (indices r) : ℝ) := by linarith
    simp [fullLabel, hc]
  · rw [hy] at hh ⊢
    norm_num at hh ⊢
    have hb := (abs_lt.mp hh).2
    have hc : ¬ (-(gamma : ℝ) / 2 ≤ (UnitMinimumCenter.score (indices r) : ℝ)) := by linarith
    simp [fullLabel, hc]

theorem origin_T (z : Space) : T 0 z = 0 := by
  simp [T, A, numeratorForm_apply, IntegerBinaryFiber.bit]

theorem origin_candidateScore (z : Space) : candidateScore 0 z = 1 := by
  simp [candidateScore, origin_T]

theorem fullLabel_origin : fullLabel 0 = 1 := by
  have hh : -(gamma : ℝ) / 2 ≤ 0 := by linarith [gamma_real_pos]
  simp [fullLabel, UnitMinimumCenter.origin_score, hh]

theorem center_score_change (v : ℕ) (z : Space) (hz : z ∈ certBall) :
    |T v z - (UnitMinimumCenter.score v : ℝ)| ≤ 1 / 10^9 := by
  have hc : center ∈ certBall := mem_closedBall_self radius_nonneg
  have hn : ‖z - center‖ ≤ radius := by simpa [certBall, mem_closedBall, dist_eq_norm] using hz
  have hh := (score_difference v z center hz hc).trans
    (mul_le_mul_of_nonneg_left hn (by positivity))
  rw [T_center] at hh
  refine hh.trans ?_
  norm_num [radius]

theorem active_slack_identity (r : Fin 108) (z : Space) :
    fullLabel (indices r) * candidateScore (indices r) z - 1 =
      (2 / (gamma : ℝ)) * ((labels r : ℝ) * F z r) := by
  rw [fullLabel_active]
  have hg := gamma_real_pos.ne'
  simp only [candidateScore, F]
  rcases active_labels_values r with hy | hy <;> rw [hy] <;> norm_num <;> field_simp
  <;> ring

theorem active_margin (z : Space) (hzero : F z = 0) (r : Fin 108) :
    fullLabel (indices r) * candidateScore (indices r) z = 1 := by
  have hh := active_slack_identity r z
  rw [hzero] at hh
  simp only [Pi.zero_apply, mul_zero] at hh
  linarith

theorem unselected_margin (v : Fin (2^18)) (hv : v.val ≠ 0)
    (ha : ¬ ∃ r, indices r = v.val) (z : Space) (hz : z ∈ certBall) :
    1 < fullLabel v.val * candidateScore v.val z := by
  have hd := abs_le.mp (center_score_change v.val z hz)
  have hg := gamma_real_pos
  have hq : 0 < 2 / (gamma : ℝ) := div_pos (by norm_num) hg
  rcases UnitMinimumCenter.unselected_score_gap v hv ha with hp | hn
  · have hc : (1 / 100000000 : ℝ) ≤ (UnitMinimumCenter.score v.val : ℝ) := by
      have hh : ((1 / 100000000 : ℚ) : ℝ) ≤ (UnitMinimumCenter.score v.val : ℝ) := Rat.cast_le.mpr hp
      norm_num at hh
      exact hh
    have hlabel : -(gamma : ℝ) / 2 ≤ (UnitMinimumCenter.score v.val : ℝ) := by linarith
    have ht : 0 < T v.val z := by linarith [hd.1]
    simp only [fullLabel, ite_eq_left hlabel, one_mul, candidateScore]
    nlinarith [mul_pos hq ht]
  · have hc : (UnitMinimumCenter.score v.val : ℝ) ≤ -(gamma : ℝ) - 1 / 100000000 := by
      have hh : (UnitMinimumCenter.score v.val : ℝ) ≤ ((-gamma - 1 / 100000000 : ℚ) : ℝ) :=
        Rat.cast_le.mpr hn
      simpa only [Rat.cast_sub, Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh
    have hlabel : ¬ (-(gamma : ℝ) / 2 ≤ (UnitMinimumCenter.score v.val : ℝ)) := by linarith
    have ht : T v.val z < -(gamma : ℝ) := by linarith [hd.2]
    have heq : 2 / (gamma : ℝ) * (gamma : ℝ) = 2 := by field_simp
    simp only [fullLabel, ite_eq_right hlabel, neg_mul, one_mul, candidateScore]
    nlinarith [mul_lt_mul_of_pos_left ht hq]

theorem full_cube_unit_margin (z : Space) (hz : z ∈ certBall) (hzero : F z = 0)
    (v : Fin (2^18)) : 1 ≤ fullLabel v.val * candidateScore v.val z := by
  by_cases hv : v.val = 0
  · simp [hv, fullLabel_origin, origin_candidateScore]
  by_cases ha : ∃ r, indices r = v.val
  · obtain ⟨r, hr⟩ := ha
    rw [← hr, active_margin z hzero r]
  · exact (unselected_margin v hv ha z hz).le

theorem full_constraints_imply_active (z : Space)
    (hfull : ∀ v : Fin (2^18), 1 ≤ fullLabel v.val * candidateScore v.val z) :
    ∀ r, 0 ≤ (labels r : ℝ) * F z r := by
  intro r
  have hh := hfull ⟨indices r, indices_bound r⟩
  have hs := active_slack_identity r z
  have hq : 0 < 2 / (gamma : ℝ) := div_pos (by norm_num) gamma_real_pos
  dsimp at hh
  nlinarith

#print axioms full_cube_unit_margin
#print axioms full_constraints_imply_active

end HeadComplexity.UnitMinimumAnalytic
