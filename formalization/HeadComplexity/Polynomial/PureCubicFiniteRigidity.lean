import HeadComplexity.Polynomial.CubicNormalization
import HeadComplexity.Polynomial.PureCubicCoefficientBounds
import HeadComplexity.Polynomial.PureCubicSignProbe
import HeadComplexity.Polynomial.SignRigidityNormalization
import HeadComplexity.Polynomial.ExplicitCubicGapConstants

set_option linter.style.header false

/-! # Finite Boolean sign rigidity for the explicit replicated cubic

Every nonzero cubic with the correct labels on the explicit finite mean grid
is, after an unrestricted scalar rescaling, closer to the target than the
uniform oriented squarefree exclusion radius.
-/

namespace HeadComplexity.PureCubicFiniteRigidity
noncomputable section
open MvPolynomial PureRoPEReplication PureCubicRawKernel PureCubicInterpolation
open CubicMonomialBasis CubicNormalization PureCubicCoefficientBounds
open PureCubicSignProbe MeanGridSignProbe ExplicitCubicGapConstants
open scoped BigOperators

theorem replication_size : (2 : ℝ)^60 ≤ replicationCount := by
  simp only [replicationCount, Nat.cast_pow, Nat.cast_ofNat]
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)

theorem replication_error_small :
    (2 : ℝ)^300000 * ((2 : ℝ)^67 / replicationCount) < squarefreeRadius / 4 := by
  have hp : (0 : ℝ) < (2 : ℝ)^400000 := pow_pos (by norm_num) _
  have h2000 : (0 : ℝ) < (2 : ℝ)^2000 := pow_pos (by norm_num) _
  simp only [replicationCount, Nat.cast_pow, Nat.cast_ofNat, squarefreeRadius]
  rw [← mul_div_assoc, ← pow_add]
  rw [div_div]
  apply (div_lt_div_iff₀ hp (mul_pos h2000 (by norm_num))).mpr
  rw [one_mul]
  have he : (2 : ℝ)^ (300000 + 67) * (2^2000 * 4) = (2 : ℝ)^302069 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, ← mul_assoc, ← pow_add, ← pow_add]
  rw [he]
  exact pow_lt_pow_right₀ (by norm_num) (by norm_num)

theorem normalized_rigidity (Q : MvPolynomial (Fin 14) ℝ)
    (hQdeg : Q.totalDegree ≤ 3) (hQc : ∀ d, |Q.coeff d| ≤ 1)
    (hQmax : ∃ j : Fin 680, |Q.coeff (exponent j)| = 1)
    (hsign : ∀ k : Fin 14 → Fin (replicationCount + 1),
      (0 < eval (fun i ↦ gridValue replicationCount (k i)) rawTarget ↔
        0 < eval (fun i ↦ gridValue replicationCount (k i)) Q)) :
    ∃ c : ℝ, 1 / 2 ≤ |c| ∧ ∀ d : Fin 14 →₀ ℕ,
      |Q.coeff d - c * rawTarget.coeff d| < |c| * squarefreeRadius := by
  let ε : ℝ := (2 : ℝ)^67 / replicationCount
  have hε : 0 < ε := div_pos (pow_pos (by norm_num) _)
    (by exact_mod_cast replicationCount_positive)
  obtain ⟨c, hc⟩ := coefficient_recovery Q hQdeg ε hε (by
    intro y hy
    exact (chart_residual_bound Q hQdeg hQc rawTarget_coefficient_bound
      replicationCount replicationCount_positive replication_size hsign y hy).le)
  let e : ℝ := (2 : ℝ)^300000 * ε
  have he : e < squarefreeRadius / 4 := replication_error_small
  have hehalf : e ≤ 1 / 2 := by
    calc
      e ≤ squarefreeRadius / 4 := he.le
      _ ≤ 1 / 4 := div_le_div_of_nonneg_right squarefreeRadius_le_one (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have habs : 1 - e ≤ |c| := SignRigidityNormalization.scalar_abs_lower
    (coefficients rawTarget) (coefficients Q) c e
    (fun j ↦ rawTarget_coefficient_bound _) hQmax (fun j ↦ (hc _).le)
  have hcabs : 1 / 2 ≤ |c| := by
    calc
      (1 / 2 : ℝ) = 1 - 1 / 2 := by norm_num
      _ ≤ 1 - e := sub_le_sub_left hehalf 1
      _ ≤ |c| := habs
  refine ⟨c, hcabs, ?_⟩
  intro d
  apply (hc d).trans
  have hmul := mul_le_mul_of_nonneg_right hcabs squarefreeRadius_pos.le
  change e < |c| * squarefreeRadius
  calc
    e < squarefreeRadius / 4 := he
    _ ≤ (1 / 2) * squarefreeRadius := by
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ)⁻¹ ≤ 1 / 2)
        squarefreeRadius_pos.le
    _ ≤ |c| * squarefreeRadius := hmul

/-- This theorem quantifies over every real cubic, without a normalization
hypothesis or a restriction on the sign of the recovered scalar. -/
theorem finite_sign_rigidity (P : MvPolynomial (Fin 14) ℝ)
    (hPdeg : P.totalDegree ≤ 3) (hP : P ≠ 0)
    (hsign : ∀ k : Fin 14 → Fin (replicationCount + 1),
      (0 < eval (fun i ↦ gridValue replicationCount (k i)) rawTarget ↔
        0 < eval (fun i ↦ gridValue replicationCount (k i)) P)) :
    ∃ a : ℝ, a ≠ 0 ∧ ∀ d : Fin 14 →₀ ℕ,
      |P.coeff d - a * rawTarget.coeff d| < |a| * squarefreeRadius := by
  obtain ⟨t, ht, hQc, hQmax⟩ := exists_positive_normalization P hPdeg hP
  obtain ⟨c, hc, herr⟩ := normalized_rigidity (C t * P)
    (positive_scale_degree P t hPdeg) hQc hQmax (by
      intro k
      exact (hsign k).trans (positive_scale_sign P t ht _).symm)
  have hcne : c ≠ 0 := by intro hz; simp only [hz, abs_zero] at hc; norm_num at hc
  refine ⟨c / t, div_ne_zero hcne ht.ne', ?_⟩
  intro d
  have h := herr d
  rw [coeff_C_mul] at h
  have he : P.coeff d - c / t * rawTarget.coeff d =
      (t * P.coeff d - c * rawTarget.coeff d) / t := by field_simp
  rw [he, abs_div, abs_div, abs_of_pos ht]
  apply (div_lt_iff₀ ht).mpr
  have hr : |c| / t * squarefreeRadius * t = |c| * squarefreeRadius := by
    field_simp
  rwa [hr]

end
end HeadComplexity.PureCubicFiniteRigidity
