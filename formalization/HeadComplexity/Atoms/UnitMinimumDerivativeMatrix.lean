import HeadComplexity.Atoms.UnitMinimumAnalyticBounds

set_option linter.style.header false

namespace HeadComplexity.UnitMinimumAnalytic

open scoped BigOperators
open ContinuousLinearMap Metric Set
open IntegerBinaryFiber (bit)
open UnitMinimumCenter (scale indices labels gamma columnHead columnInput)
open FiniteRatioCalculus

theorem numeratorIndex_eq_iff (i : Fin 18) (h : Fin 3) (c : Fin 108) :
    numeratorIndex i h = c ↔ c.val < 54 ∧ columnHead c = h ∧ columnInput c = i := by
  constructor
  · rintro rfl
    exact ⟨numeratorIndex_lt i h, (index_columns i h).1, (index_columns i h).2.1⟩
  · intro hc
    have hi := i.isLt
    have hh := h.isLt
    have hhead := congrArg Fin.val hc.2.1
    have hinput := congrArg Fin.val hc.2.2
    apply Fin.ext
    simp only [columnHead, columnInput, numeratorIndex] at *
    omega

theorem denominatorIndex_eq_iff (i : Fin 18) (h : Fin 3) (c : Fin 108) :
    denominatorIndex i h = c ↔ 54 ≤ c.val ∧ columnHead c = h ∧ columnInput c = i := by
  constructor
  · rintro rfl
    exact ⟨denominatorIndex_ge i h, (index_columns i h).2.2.1, (index_columns i h).2.2.2⟩
  · intro hc
    have hi := i.isLt
    have hh := h.isLt
    have hcc := c.isLt
    have hhead := congrArg Fin.val hc.2.1
    have hinput := congrArg Fin.val hc.2.2
    apply Fin.ext
    simp only [columnHead, columnInput, denominatorIndex] at *
    omega

theorem numeratorForm_single (h : Fin 3) (v : ℕ) (c : Fin 108) :
    numeratorForm h v (Pi.single c 1) =
      if c.val < 54 ∧ columnHead c = h then (bit v (columnInput c).val : ℝ) else 0 := by
  classical
  rw [numeratorForm_apply]
  have hh (i : Fin 18) :
      (bit v i.val : ℝ) * (Pi.single c 1 : Space) (numeratorIndex i h) =
      if c.val < 54 ∧ columnHead c = h ∧ columnInput c = i then (bit v i.val : ℝ) else 0 := by
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
    simp only [numeratorIndex_eq_iff]
  simp_rw [hh]
  by_cases hc : c.val < 54 ∧ columnHead c = h
  · simp [hc.1, hc.2]
  · have hn (i : Fin 18) : ¬ (c.val < 54 ∧ columnHead c = h ∧ columnInput c = i) := by
      tauto
    simp [hc, hn]

theorem denominatorForm_single (h : Fin 3) (v : ℕ) (c : Fin 108) :
    denominatorForm h v (Pi.single c 1) =
      if 54 ≤ c.val ∧ columnHead c = h then (bit v (columnInput c).val : ℝ) else 0 := by
  classical
  rw [denominatorForm_apply]
  have hh (i : Fin 18) :
      (bit v i.val : ℝ) * (Pi.single c 1 : Space) (denominatorIndex i h) =
      if 54 ≤ c.val ∧ columnHead c = h ∧ columnInput c = i then (bit v i.val : ℝ) else 0 := by
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
    simp only [denominatorIndex_eq_iff]
  simp_rw [hh]
  by_cases hc : 54 ≤ c.val ∧ columnHead c = h
  · simp [hc.1, hc.2]
  · have hn (i : Fin 18) : ¬ (54 ≤ c.val ∧ columnHead c = h ∧ columnInput c = i) := by
      tauto
    simp [hc, hn]

noncomputable def jacobianEntry (v : ℕ) (z : Space) (c : Fin 108) : ℝ :=
  let h := columnHead c
  let x : ℝ := bit v (columnInput c).val
  if c.val < 54 then x / B h v z else -x * A h v z / (B h v z)^2

theorem scoreDerivative_single (v : ℕ) (z : Space) (c : Fin 108) :
    scoreDerivative v z (Pi.single c 1) = jacobianEntry v z c := by
  classical
  simp only [scoreDerivative, sum_apply, sub_apply, smul_apply, smul_eq_mul,
    numeratorForm_single, denominatorForm_single]
  rw [Finset.sum_eq_single (columnHead c)]
  · by_cases hc : c.val < 54
    · simp [jacobianEntry, hc, not_le.mpr hc, div_eq_mul_inv, mul_comm]
    · simp [jacobianEntry, hc, le_of_not_gt hc]
      ring
  · intro h _ hh
    simp [Ne.symm hh]
  · simp

noncomputable def F (z : Space) : Space := fun r ↦
  T (indices r) z + if labels r < 0 then (gamma : ℝ) else 0

noncomputable def J (z : Space) : Space →L[ℝ] Space :=
  ContinuousLinearMap.pi fun r ↦ scoreDerivative (indices r) z

theorem J_single (z : Space) (r c : Fin 108) :
    J z (Pi.single c 1) r = jacobianEntry (indices r) z c := scoreDerivative_single ..

theorem hasFDerivAt_F (z : Space) (hz : z ∈ certBall) : HasFDerivAt F (J z) z := by
  apply hasFDerivAt_pi.mpr
  intro r
  exact (hasFDerivAt_T (indices r) z (fun h ↦ (beta_pos.trans (B_bound h _ z hz)).ne')).add_const _

theorem F_center_bound : ‖F center‖ ≤ 1 / 10^60 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 10^60)).2
  intro r
  rw [Real.norm_eq_abs]
  have hh := UnitMinimumCenter.active_residual r
  have hcast : |(UnitMinimumCenter.score (indices r) : ℝ) +
      if labels r < 0 then (gamma : ℝ) else 0| < (1 / 10^60 : ℝ) := by
    have hc : ((|UnitMinimumCenter.score (indices r) +
        if labels r < 0 then gamma else 0| : ℚ) : ℝ) < ((1 / 10^60 : ℚ) : ℝ) := by
      exact Rat.cast_lt.mpr hh
    split_ifs at hc ⊢ <;> simpa only [Rat.cast_abs, Rat.cast_add, Rat.cast_zero,
      Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hc
  simpa only [F, T_center] using hcast.le

theorem J_center_entry (r c : Fin 108) :
    jacobianEntry (indices r) center c =
      (UnitMinimumCenter.jacobianNumerator r c : ℝ) / UnitMinimumCenter.jacobianDenominator r c := by
  have hs : (scale : ℝ) ≠ 0 := by norm_num [scale]
  have hd : (UnitMinimumCenter.den (columnHead c) (indices r) : ℝ) ≠ 0 := by
    exact_mod_cast (UnitMinimumCenter.den_positive (columnHead c) (indices r)).ne'
  simp only [jacobianEntry, A_center, B_center, UnitMinimumCenter.jacobianNumerator,
    UnitMinimumCenter.jacobianDenominator]
  split_ifs <;> push_cast <;> field_simp

#print axioms hasFDerivAt_F
#print axioms J_center_entry

end HeadComplexity.UnitMinimumAnalytic
