import HeadComplexity.Atoms.UnitMinimumPositiveMultipliers
import HeadComplexity.Atoms.UnitMinimumMargins

set_option linter.style.header false

/-!
A concrete strict local minimum of the full Boolean-cube unit-margin problem.
The 18-bit cube is enumerated by `Fin (2^18)` and its bits are the exact integer
bits used by the input numerator and denominator forms. The result below does
not assert global minimality and does not assert a worst-case head lower bound.
-/

namespace HeadComplexity.UnitMinimumAnalytic

open scoped BigOperators Topology
open ContinuousLinearMap Metric Set Filter
open UnitMinimumCenter (indices labels gamma)

noncomputable def normalizedObjective (z : Space) : ℝ :=
  (1 / 2) * ∑ c : Fin 108, if c.val < 54 then ((2 / (gamma : ℝ)) * z c)^2 else 0

theorem normalizedObjective_eq (z : Space) :
    normalizedObjective z = (2 / (gamma : ℝ))^2 * objective z := by
  simp only [normalizedObjective, objective, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> ring

set_option maxHeartbeats 1000000 in
theorem root_strict_minimum (z : Space) (hz : z ∈ certBall) (hzero : F z = 0) :
    ∀ᶠ w in 𝓝 z, w ≠ z →
      (∀ v : Fin (2^18), 1 ≤ fullLabel v.val * candidateScore v.val w) →
      normalizedObjective z < normalizedObjective w := by
  obtain ⟨lam, hlam, hstationary⟩ := exists_positive_multipliers z hz
  let g : Space → Space := fun w ↦ signMap (F w)
  have hg : g z = 0 := by simp [g, hzero]
  have he : (signedEquiv z hz).toContinuousLinearMap = signedJacobian z := by
    ext w
    rfl
  have hder : HasFDerivAt g (signedEquiv z hz).toContinuousLinearMap z := by
    rw [he]
    exact signMap.hasFDerivAt.comp z (hasFDerivAt_F z hz)
  have hobj : HasFDerivAt objective
      ((CertifiedContraction.positiveFunctional lam).comp (signedEquiv z hz).toContinuousLinearMap) z := by
    rw [hstationary]
    exact hasFDerivAt_objective z
  have hmin := CertifiedContraction.strict_local_minimum_of_positive_multipliers
    g objective z (signedEquiv z hz) lam (1 / 1000) (by norm_num) hlam hg hder hobj
  filter_upwards [hmin] with w hw hne hfull
  have hfeas : ∀ r, 0 ≤ g w r := by
    intro r
    exact full_constraints_imply_active w hfull r
  have hlt := hw hne hfeas
  rw [normalizedObjective_eq, normalizedObjective_eq]
  exact mul_lt_mul_of_pos_left hlt (sq_pos_of_pos (div_pos (by norm_num) gamma_real_pos))

/-- The complete concrete analytic counterexample. It has coherent negative
denominators, all cube margins, and 108 independent active gradients. -/
theorem exists_full_cube_strict_minimum :
    ∃ z ∈ certBall,
      (∀ i h, z (denominatorIndex i h) < 0) ∧
      (∀ h v, 0 < B h v z) ∧
      (∀ v : Fin (2^18), 1 ≤ fullLabel v.val * candidateScore v.val z) ∧
      (∀ r, fullLabel (indices r) * candidateScore (indices r) z = 1) ∧
      Function.Injective (J z) ∧
      (∀ᶠ w in 𝓝 z, w ≠ z →
        (∀ v : Fin (2^18), 1 ≤ fullLabel v.val * candidateScore v.val w) →
        normalizedObjective z < normalizedObjective w) := by
  obtain ⟨z, hz, hzero, hinj⟩ := exists_certified_root
  refine ⟨z, hz, ?_, ?_, full_cube_unit_margin z hz hzero, active_margin z hzero, hinj,
    root_strict_minimum z hz hzero⟩
  · exact slope_negative z hz
  · intro h v
    exact beta_pos.trans (B_bound h v z hz)

#print axioms root_strict_minimum
#print axioms exists_full_cube_strict_minimum

end HeadComplexity.UnitMinimumAnalytic
