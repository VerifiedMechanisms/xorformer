import HeadComplexity.Polynomial.PureCubicFiniteRigidity
import HeadComplexity.Polynomial.ThreeHeadMeanGap
import HeadComplexity.Polynomial.ParityThresholdDegree
import HeadComplexity.Polynomial.ReplicatedThresholdMean

set_option linter.style.header false

/-! # Threshold degree of the explicit pure RoPE separation -/

namespace HeadComplexity.PureRoPEExplicitThreshold
noncomputable section
open scoped BigOperators
open MvPolynomial PureRoPEReplication PureRoPEReplicationStrict
open PureCubicRawKernel PureCubicFiniteRigidity MeanGridSignProbe
open ExplicitCubicGapConstants ExplicitCubicSquarefreeGap GenericCubicHessianPullback

/-- The target has a squarefree cubic coefficient larger than the exclusion
radius, by applying the universal coefficient gap to the zero competitor. -/
theorem target_large_squarefree :
    ∃ i j k : Fin 14, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ squarefreeRadius <
      |rawTarget.coeff
        (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1)| := by
  obtain ⟨i, j, k, hij, hik, hjk, hgap⟩ := squarefree_coefficient_gap
    (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fun _ ↦ Or.inr (Or.inr rfl))
  refine ⟨i, j, k, hij, hik, hjk, ?_⟩
  rw [ThreeHeadMeanGap.rawTarget_top_coefficient i j k hij hik hjk]
  simpa [cubic, linearPolynomial] using hgap

/-- No real polynomial of degree at most two has the target classifier on the
full explicit mean grid. No symmetry or parameter assumptions are imposed. -/
theorem not_quadratic_grid_classifier (Q : MvPolynomial (Fin 14) ℝ)
    (hQ : Q.totalDegree ≤ 2) (hQne : Q ≠ 0)
    (hsign : ∀ k : Fin 14 → Fin (replicationCount + 1),
      (0 < eval (fun i ↦ gridValue replicationCount (k i)) rawTarget ↔
        0 < eval (fun i ↦ gridValue replicationCount (k i)) Q)) : False := by
  obtain ⟨a, ha, hclose⟩ := finite_sign_rigidity Q (by omega) hQne hsign
  obtain ⟨i, j, k, hij, hik, hjk, hlarge⟩ := target_large_squarefree
  let d := Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1
  have hdegree : d.degree = 3 := by
    simp [d, map_add]
  have hzero : Q.coeff d = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    change Q.totalDegree < d.degree
    omega
  have hnear := hclose d
  rw [hzero, zero_sub, abs_neg, abs_mul] at hnear
  have hfar := mul_lt_mul_of_pos_left hlarge (abs_pos.mpr ha)
  exact (not_lt_of_ge hnear.le) hfar


theorem replication_gt_two : 2 < replicationCount := by
  have h : 4 ≤ replicationCount := by
    change 2 ^ 2 ≤ 2 ^ 400000
    exact Nat.pow_le_pow_right (n := 2) (i := 2) (j := 400000) (by decide) (by decide)
  omega

/-- The lower bound quantifies over all real threshold polynomials on all
fourteen replicated bit groups, without a symmetry restriction. -/
theorem not_thresholdDegLE_two : ¬ ThresholdDegLE explicitUnshiftedFunction 2 := by
  intro h
  obtain ⟨Q, hQ, hQne, hsign⟩ :=
    ReplicatedThresholdMean.threshold_two_mean replication_gt_two h
  exact not_quadratic_grid_classifier Q hQ hQne hsign

theorem thresholdDeg_eq_three : thresholdDeg explicitUnshiftedFunction = 3 := by
  classical
  have hex : ∃ d, ThresholdDegLE explicitUnshiftedFunction d :=
    ⟨3, explicitUnshiftedFunction_thresholdDegLE⟩
  rw [thresholdDeg, dif_pos hex]
  apply Nat.le_antisymm (Nat.find_min' hex explicitUnshiftedFunction_thresholdDegLE)
  by_contra h
  have hfind : Nat.find hex ≤ 2 := by omega
  obtain ⟨P, hPdeg, hPsign⟩ := Nat.find_spec hex
  exact not_thresholdDegLE_two ⟨P, hPdeg.trans hfind, hPsign⟩

end
end HeadComplexity.PureRoPEExplicitThreshold
