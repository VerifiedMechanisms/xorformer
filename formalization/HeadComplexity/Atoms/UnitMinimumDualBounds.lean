import HeadComplexity.Atoms.UnitMinimumInverseBounds

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxRecDepth 100000

namespace HeadComplexity.UnitMinimumAnalytic

open scoped BigOperators
open ContinuousLinearMap Metric Set
open UnitMinimumCenter (scale labels dualInteger gradientInteger roundedJacobian)
open FiniteRatioCalculus

theorem labels_values (r : Fin 108) : labels r = 1 ∨ labels r = -1 := by
  fin_cases r <;> decide +kernel

theorem labels_abs (r : Fin 108) : |(labels r : ℝ)| = 1 := by
  rcases labels_values r with hh | hh <;> rw [hh] <;> norm_num

noncomputable def signMap : Space →L[ℝ] Space :=
  ContinuousLinearMap.pi fun r ↦ (labels r : ℝ) • ContinuousLinearMap.proj r

theorem signMap_apply (z : Space) (r : Fin 108) : signMap z r = (labels r : ℝ) * z r := by
  simp [signMap]

theorem signMap_norm : ‖signMap‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2
  intro r
  rw [Real.norm_eq_abs, signMap_apply, abs_mul, labels_abs, one_mul]
  simpa using norm_le_pi_norm z r

theorem signMap_squared : signMap.comp signMap = ContinuousLinearMap.id ℝ Space := by
  ext z r
  simp only [comp_apply, signMap_apply, id_apply]
  rcases labels_values r with hh | hh <;> rw [hh] <;> simp

noncomputable def dualCenter : Space := fun r ↦ (dualInteger r : ℝ) / scale

noncomputable def dualCenterForm : Space →L[ℝ] ℝ := rowForm dualCenter

theorem dualCenter_lower (r : Fin 108) : 3 / 1000 < dualCenter r := by
  unfold dualCenter
  apply (lt_div_iff₀ scale_real_pos).mpr
  have hh : 3 * (scale : ℝ) < 1000 * (dualInteger r : ℝ) := by
    exact_mod_cast (UnitMinimumCenter.dual_bounds r).1
  linarith

theorem dualCenter_upper (r : Fin 108) : dualCenter r < 1000000 := by
  unfold dualCenter
  apply (div_lt_iff₀ scale_real_pos).mpr
  exact_mod_cast (UnitMinimumCenter.dual_bounds r).2

theorem dualCenterForm_norm : ‖dualCenterForm‖ ≤ 108 * 1000000 := by
  refine (rowForm_norm dualCenter).trans ?_
  calc
    ∑ r, |dualCenter r| ≤ ∑ _ : Fin 108, (1000000 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_of_pos (lt_trans (by norm_num) (dualCenter_lower r))]
      exact (dualCenter_upper r).le
    _ = 108 * 1000000 := by norm_num

noncomputable def gradient (z : Space) (c : Fin 108) : ℝ := if c.val < 54 then z c else 0

noncomputable def gradientForm (z : Space) : Space →L[ℝ] ℝ := rowForm (gradient z)

noncomputable def objective (z : Space) : ℝ := (1 / 2) * ∑ c : Fin 108,
  if c.val < 54 then (z c)^2 else 0

theorem hasFDerivAt_objective (z : Space) : HasFDerivAt objective (gradientForm z) z := by
  have hsum : HasFDerivAt (fun w : Space ↦ ∑ c : Fin 108,
      if c.val < 54 then (w c)^2 else 0)
      (∑ c : Fin 108, if c.val < 54 then
        (2 * z c) • (ContinuousLinearMap.proj c : Space →L[ℝ] ℝ) else 0) z := by
    apply HasFDerivAt.fun_sum
    intro c _
    split_ifs with hc
    · have hh := ((ContinuousLinearMap.proj c : Space →L[ℝ] ℝ).hasFDerivAt (x := z)).mul
        ((ContinuousLinearMap.proj c : Space →L[ℝ] ℝ).hasFDerivAt (x := z))
      convert hh using 1
      · ext w
        simp [pow_two]
      · ext w
        simp
        ring
    · exact hasFDerivAt_const 0 z
  convert hsum.const_mul (1 / 2 : ℝ) using 1
  · rfl
  · ext w
    simp only [gradientForm, rowForm_apply, gradient, smul_apply, smul_eq_mul, sum_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp <;> ring

theorem gradient_center (c : Fin 108) : gradient center c = (gradientInteger c : ℝ) / scale := by
  simp only [gradient, center, gradientInteger]
  split_ifs <;> simp_all

theorem gradient_difference (z w : Space) : ‖gradientForm z - gradientForm w‖ ≤ 108 * ‖z - w‖ := by
  have heq : gradientForm z - gradientForm w = rowForm (fun c ↦ gradient z c - gradient w c) := by
    ext t
    simp [gradientForm, rowForm_apply, Finset.sum_sub_distrib, sub_mul]
  rw [heq]
  refine (rowForm_norm _).trans ?_
  calc
    ∑ c, |gradient z c - gradient w c| ≤ ∑ _ : Fin 108, ‖z - w‖ := by
      apply Finset.sum_le_sum
      intro c _
      simp only [gradient]
      split_ifs
      · simpa using norm_le_pi_norm (z - w) c
      · simp
    _ = 108 * ‖z - w‖ := by simp

theorem rounded_dual_entry (c : Fin 108) :
    |(dualCenterForm.comp (signMap.comp roundedMap) - gradientForm center) (Pi.single c 1)| ≤
      1 / 10^55 := by
  have heq : (dualCenterForm.comp (signMap.comp roundedMap) - gradientForm center) (Pi.single c 1) =
      (((∑ r : Fin 108, roundedJacobian r c * labels r * dualInteger r) -
        scale * gradientInteger c : ℤ) : ℝ) / (scale : ℝ)^2 := by
    simp only [sub_apply, comp_apply, dualCenterForm, rowForm_apply, gradientForm,
      signMap_apply, roundedMap, matrixMap_apply]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, gradient_center, dualCenter]
    push_cast
    rw [sub_div, Finset.sum_div]
    congr 1
    · apply Finset.sum_congr rfl
      intro r _
      ring
    · field_simp
  rw [heq, abs_div, abs_of_nonneg (sq_nonneg (scale : ℝ)), ← Int.cast_abs]
  apply (div_le_iff₀ (sq_pos_of_pos scale_real_pos)).mpr
  have hh : (10 : ℝ)^55 * |(((∑ r : Fin 108, roundedJacobian r c * labels r * dualInteger r) -
        scale * gradientInteger c : ℤ) : ℝ)| < (scale : ℝ)^2 := by
    exact_mod_cast UnitMinimumCenter.dual_residual c
  rw [← Int.cast_abs] at hh
  linarith

theorem rounded_dual_norm :
    ‖dualCenterForm.comp (signMap.comp roundedMap) - gradientForm center‖ ≤ 108 / 10^55 := by
  rw [← rowForm_of_basis_values
    (dualCenterForm.comp (signMap.comp roundedMap) - gradientForm center)]
  refine (rowForm_norm _).trans ?_
  calc
    ∑ c, |(dualCenterForm.comp (signMap.comp roundedMap) - gradientForm center) (Pi.single c 1)| ≤
        ∑ _ : Fin 108, (1 / 10^55 : ℝ) := Finset.sum_le_sum fun c _ ↦ rounded_dual_entry c
    _ = 108 / 10^55 := by norm_num

#print axioms hasFDerivAt_objective
#print axioms rounded_dual_norm

end HeadComplexity.UnitMinimumAnalytic
