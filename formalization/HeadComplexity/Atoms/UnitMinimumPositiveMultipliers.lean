import HeadComplexity.Atoms.UnitMinimumDualBounds

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxRecDepth 100000

namespace HeadComplexity.UnitMinimumAnalytic

open scoped BigOperators
open ContinuousLinearMap Metric Set
open FiniteRatioCalculus

theorem weighted_comp_bound (K : Space →L[ℝ] Space) (δ : ℝ) (hK : ‖K‖ ≤ δ) :
    ‖dualCenterForm.comp (signMap.comp K)‖ ≤ (108 * 1000000) * δ := by
  have hd : 0 ≤ δ := (norm_nonneg _).trans hK
  have hsign := (opNorm_comp_le signMap K).trans
    (mul_le_mul signMap_norm hK (norm_nonneg _) zero_le_one)
  rw [one_mul] at hsign
  exact (opNorm_comp_le dualCenterForm (signMap.comp K)).trans
    (mul_le_mul dualCenterForm_norm hsign (norm_nonneg _) (by norm_num))

theorem center_dual_residual :
    ‖dualCenterForm.comp (signMap.comp (J center)) - gradientForm center‖ ≤ 1 / 10^45 := by
  have heq : dualCenterForm.comp (signMap.comp (J center)) - gradientForm center =
      (dualCenterForm.comp (signMap.comp roundedMap) - gradientForm center) +
      dualCenterForm.comp (signMap.comp (J center - roundedMap)) := by
    ext t
    simp
  rw [heq]
  refine (norm_add_le _ _).trans <| (add_le_add rounded_dual_norm
    (weighted_comp_bound _ _ J_center_rounding_norm)).trans ?_
  norm_num [UnitMinimumCenter.scale]

theorem nearby_dual_residual (z : Space) (hz : z ∈ certBall) :
    ‖gradientForm z - dualCenterForm.comp (signMap.comp (J z))‖ ≤ 1 / 10^16 := by
  have hc : center ∈ certBall := mem_closedBall_self radius_nonneg
  have hn : ‖z - center‖ ≤ radius := by simpa [certBall, mem_closedBall, dist_eq_norm] using hz
  have hJ : ‖J z - J center‖ ≤ 10^15 * radius :=
    (J_difference z center hz hc).trans (mul_le_mul_of_nonneg_left hn (by positivity))
  have hg : ‖gradientForm z - gradientForm center‖ ≤ 108 * radius :=
    (gradient_difference z center).trans (mul_le_mul_of_nonneg_left hn (by positivity))
  rw [norm_sub_rev]
  have heq : dualCenterForm.comp (signMap.comp (J z)) - gradientForm z =
      ((dualCenterForm.comp (signMap.comp (J center)) - gradientForm center) +
        dualCenterForm.comp (signMap.comp (J z - J center))) -
      (gradientForm z - gradientForm center) := by
    ext t
    simp
  rw [heq]
  refine (norm_sub_le _ _).trans <| (add_le_add
    ((norm_add_le _ _).trans (add_le_add center_dual_residual (weighted_comp_bound _ _ hJ))) hg).trans ?_
  norm_num [radius]

noncomputable def signedJacobian (z : Space) : Space →L[ℝ] Space := signMap.comp (J z)
noncomputable def signedInverse : Space →L[ℝ] Space := inverseMap.comp signMap

theorem signedInverse_norm : ‖signedInverse‖ ≤ 100000 := by
  exact (opNorm_comp_le inverseMap signMap).trans <| by
    have hh := mul_le_mul inverseMap_norm signMap_norm (norm_nonneg _) (by norm_num)
    simpa using hh

theorem signed_residual (z : Space) (hz : z ∈ certBall) :
    ‖ContinuousLinearMap.id ℝ Space - signedInverse.comp (signedJacobian z)‖ ≤ 1 / 2 := by
  have heq : signedInverse.comp (signedJacobian z) = inverseMap.comp (J z) := by
    rw [signedInverse, signedJacobian, ← comp_assoc, comp_assoc inverseMap signMap signMap,
      signMap_squared]
    simp
  rw [heq]
  have hc : center ∈ certBall := mem_closedBall_self radius_nonneg
  have hn : ‖z - center‖ ≤ radius := by simpa [certBall, mem_closedBall, dist_eq_norm] using hz
  have hJ : ‖J z - J center‖ ≤ 10^15 * radius :=
    (J_difference z center hz hc).trans (mul_le_mul_of_nonneg_left hn (by positivity))
  have hh := ApproximateInverse.residual_near inverseMap (J z) (J center)
    (1 / 10^50) 100000 (10^15 * radius) inverse_center_residual inverseMap_norm hJ
  refine hh.trans ?_
  norm_num [radius]

noncomputable def signedEquiv (z : Space) (hz : z ∈ certBall) : Space ≃L[ℝ] Space :=
  ApproximateInverse.equivOfResidual signedInverse (signedJacobian z) (1 / 2)
    (by norm_num) (signed_residual z hz)

theorem signedEquiv_apply (z : Space) (hz : z ∈ certBall) (w : Space) :
    signedEquiv z hz w = signedJacobian z w := rfl

theorem signedEquiv_inverse_norm (z : Space) (hz : z ∈ certBall) :
    ‖(signedEquiv z hz).symm.toContinuousLinearMap‖ ≤ 200000 := by
  have hh := ApproximateInverse.inverse_norm_bound signedInverse (signedJacobian z)
    (1 / 2) 100000 (by norm_num) (signed_residual z hz) signedInverse_norm
  norm_num at hh
  exact hh

set_option maxHeartbeats 1000000 in
theorem exists_positive_multipliers (z : Space) (hz : z ∈ certBall) :
    ∃ lam : Fin 108 → ℝ, (∀ r, 1 / 1000 ≤ lam r) ∧
      (CertifiedContraction.positiveFunctional lam).comp (signedEquiv z hz).toContinuousLinearMap =
        gradientForm z := by
  let e := signedEquiv z hz
  let L : Space →L[ℝ] ℝ := (gradientForm z).comp e.symm.toContinuousLinearMap
  let lam : Fin 108 → ℝ := fun r ↦ L (Pi.single r 1)
  have hL : CertifiedContraction.positiveFunctional lam = L := rowForm_of_basis_values L
  have heq : L - dualCenterForm =
      (gradientForm z - dualCenterForm.comp (signedJacobian z)).comp e.symm.toContinuousLinearMap := by
    ext w
    have hi : signedJacobian z (e.symm w) = w := e.apply_symm_apply w
    change (gradientForm z) (e.symm w) - dualCenterForm w =
      (gradientForm z) (e.symm w) - dualCenterForm (signedJacobian z (e.symm w))
    rw [hi]
  have hdist : ‖L - dualCenterForm‖ ≤ 1 / 1000 := by
    rw [heq]
    refine (opNorm_comp_le _ _).trans <| (mul_le_mul (nearby_dual_residual z hz)
      (signedEquiv_inverse_norm z hz) (norm_nonneg _) (by norm_num)).trans ?_
    norm_num [signedJacobian]
  refine ⟨lam, ?_, ?_⟩
  · intro r
    have hsingle : ‖(Pi.single r 1 : Space)‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).2
      intro c
      simp only [Pi.single_apply, Real.norm_eq_abs]
      split_ifs <;> norm_num
    have hh := (L - dualCenterForm).le_opNorm (Pi.single r 1)
    have hb := mul_le_mul hdist hsingle (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 1000)
    have hc : |lam r - dualCenter r| ≤ 1 / 1000 := by
      simpa [lam, dualCenterForm, rowForm_apply, Pi.single_apply, Real.norm_eq_abs] using hh.trans hb
    have hlo := dualCenter_lower r
    have hl := (abs_le.mp hc).1
    linarith
  · rw [hL]
    ext w
    change gradientForm z (e.symm (e w)) = gradientForm z w
    rw [e.symm_apply_apply]

#print axioms nearby_dual_residual
#print axioms exists_positive_multipliers

end HeadComplexity.UnitMinimumAnalytic
