import HeadComplexity.Atoms.UnitMinimumDerivativeMatrix
import HeadComplexity.Atoms.FiniteMatrixNorm

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxRecDepth 100000

namespace HeadComplexity.UnitMinimumAnalytic

open scoped BigOperators
open ContinuousLinearMap Metric Set
open UnitMinimumCenter (scale inverseInteger roundedJacobian jacobianNumerator jacobianDenominator)
open FiniteRatioCalculus

noncomputable def inverseMap : Space →L[ℝ] Space :=
  matrixMap fun r c ↦ (inverseInteger r c : ℝ) / scale

noncomputable def roundedMap : Space →L[ℝ] Space :=
  matrixMap fun r c ↦ (roundedJacobian r c : ℝ) / scale

theorem scale_real_pos : (0 : ℝ) < scale := by norm_num [scale]

theorem inverseMap_norm : ‖inverseMap‖ ≤ 100000 := by
  apply matrixMap_norm _ _ (by norm_num)
  intro r
  simp only [abs_div, abs_of_pos scale_real_pos, ← Finset.sum_div, ← Int.cast_abs, ← Int.cast_sum]
  apply (div_le_iff₀ scale_real_pos).mpr
  exact_mod_cast (UnitMinimumCenter.inverse_row_bound r).le

theorem normalized_rounding_bound {D d a j : ℝ} (hD : 0 < D) (hd : 0 < d)
    (herr : 2 * |D * a - j * d| ≤ d) : |a / d - j / D| ≤ 1 / (2 * D) := by
  have heq : a / d - j / D = (D * a - j * d) / (D * d) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hD hd)]
  apply (div_le_iff₀ (mul_pos hD hd)).mpr
  have hr : 1 / (2 * D) * (D * d) = d / 2 := by field_simp
  rw [hr]
  linarith

theorem jacobian_entry_rounding_bound (r c : Fin 108) :
    |jacobianEntry (UnitMinimumCenter.indices r) center c - (roundedJacobian r c : ℝ) / scale| ≤
      1 / (2 * scale) := by
  rw [J_center_entry]
  have hh := UnitMinimumCenter.rounded_jacobian_error r c
  apply normalized_rounding_bound scale_real_pos
    (by exact_mod_cast hh.1 : (0 : ℝ) < jacobianDenominator r c)
  exact_mod_cast hh.2

theorem J_matrix (z : Space) :
    J z = matrixMap (fun r c ↦ jacobianEntry (UnitMinimumCenter.indices r) z c) := by
  have hh := matrixMap_of_basis_values (J z)
  simpa only [J_single] using hh.symm

theorem J_center_rounding_norm : ‖J center - roundedMap‖ ≤ 108 / (2 * scale) := by
  rw [J_matrix, roundedMap, ← matrixMap_sub]
  have hh := matrixMap_entry_bound
    (fun r c ↦ jacobianEntry (UnitMinimumCenter.indices r) center c -
      (roundedJacobian r c : ℝ) / scale)
    (1 / (2 * scale)) (by have := scale_real_pos; positivity) jacobian_entry_rounding_bound
  simpa [div_eq_mul_inv] using hh

theorem inverse_rounded_residual :
    ‖ContinuousLinearMap.id ℝ Space - inverseMap.comp roundedMap‖ ≤ 1 / 10^55 := by
  rw [inverseMap, roundedMap, matrixMap_comp, ← matrixMap_identity, ← matrixMap_sub]
  apply matrixMap_norm _ _ (by norm_num)
  intro r
  have hentry (c : Fin 108) :
      (if r = c then (1 : ℝ) else 0) -
        ∑ j, (inverseInteger r j : ℝ) / scale * ((roundedJacobian j c : ℝ) / scale) =
      (((if r = c then scale^2 else 0) -
        ∑ j, inverseInteger r j * roundedJacobian j c : ℤ) : ℝ) / (scale : ℝ)^2 := by
    push_cast
    rw [sub_div, Finset.sum_div]
    congr 1
    · split_ifs <;> simp [scale_real_pos.ne']
    · apply Finset.sum_congr rfl
      intro j _
      ring
  simp_rw [hentry]
  simp only [abs_div, abs_of_nonneg (sq_nonneg (scale : ℝ)), ← Finset.sum_div,
    ← Int.cast_abs, ← Int.cast_sum]
  apply (div_le_iff₀ (sq_pos_of_pos scale_real_pos)).mpr
  have hh : (10 : ℝ)^55 * (UnitMinimumCenter.inverseErrorRow r : ℝ) < (scale : ℝ)^2 := by
    exact_mod_cast UnitMinimumCenter.inverse_error_rows r
  change (UnitMinimumCenter.inverseErrorRow r : ℝ) ≤ _
  linarith

theorem inverse_center_residual :
    ‖ContinuousLinearMap.id ℝ Space - inverseMap.comp (J center)‖ ≤ 1 / 10^50 := by
  have hh := ApproximateInverse.residual_near inverseMap (J center) roundedMap
    (1 / 10^55) 100000 (108 / (2 * scale)) inverse_rounded_residual inverseMap_norm J_center_rounding_norm
  refine hh.trans ?_
  norm_num [scale]

theorem J_difference (z w : Space) (hz : z ∈ certBall) (hw : w ∈ certBall) :
    ‖J z - J w‖ ≤ 10^15 * ‖z - w‖ := by
  have heq : J z - J w = ContinuousLinearMap.pi
      (fun r ↦ scoreDerivative (UnitMinimumCenter.indices r) z -
        scoreDerivative (UnitMinimumCenter.indices r) w) := by
    ext t r
    simp [J]
  rw [heq]
  apply piMap_norm_bound _ _ (by positivity)
  intro r
  exact derivative_difference _ z w hz hw

theorem exists_certified_root : ∃ z ∈ certBall, F z = 0 ∧ Function.Injective (J z) := by
  have hc : center ∈ certBall := mem_closedBall_self radius_nonneg
  apply ApproximateInverse.exists_zero_of_derivative_certificate F J inverseMap center
    radius (1 / 10^50) 100000 (10^15 * radius) (1 / 2) radius_nonneg (by norm_num)
  · exact hasFDerivAt_F
  · exact inverse_center_residual
  · exact inverseMap_norm
  · intro z hz
    have hn : ‖z - center‖ ≤ radius := by simpa [certBall, mem_closedBall, dist_eq_norm] using hz
    exact (J_difference z center hz hc).trans (mul_le_mul_of_nonneg_left hn (by positivity))
  · norm_num [radius]
  · have hh := inverseMap.le_opNorm (F center)
    have hb := mul_le_mul inverseMap_norm F_center_bound (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 100000)
    refine (hh.trans hb).trans ?_
    norm_num [radius]

#print axioms inverse_center_residual
#print axioms exists_certified_root

end HeadComplexity.UnitMinimumAnalytic
