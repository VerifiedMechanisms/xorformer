import HeadComplexity.Polynomial.PureCubicInterpolation
import Mathlib.Data.Finset.Max

set_option linter.style.header false

/-! # Positive coefficient normalization of a nonzero cubic -/

namespace HeadComplexity.CubicNormalization
noncomputable section
open MvPolynomial CubicMonomialBasis PureCubicInterpolation
open scoped BigOperators

theorem exists_positive_normalization (P : MvPolynomial (Fin 14) ℝ)
    (hdeg : P.totalDegree ≤ 3) (hP : P ≠ 0) :
    ∃ t : ℝ, 0 < t ∧
      (∀ d, |(C t * P).coeff d| ≤ 1) ∧
      (∃ j : Fin 680, |(C t * P).coeff (exponent j)| = 1) := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 680))
    (fun j ↦ |P.coeff (exponent j)|) (by simp)
  let M := |P.coeff (exponent j)|
  have hmax (d : Fin 14 →₀ ℕ) : |P.coeff d| ≤ M := by
    by_cases hd : d.sum (fun _ k ↦ k) ≤ 3
    · obtain ⟨i, rfl⟩ := exponent_surjective d hd
      exact hj i (Finset.mem_univ _)
    · have hz : P.coeff d = 0 := coeff_eq_zero_of_totalDegree_lt
        (hdeg.trans_lt (Nat.lt_of_not_ge hd))
      rw [hz, abs_zero]
      exact abs_nonneg _
  have hM : 0 < M := by
    by_contra hm
    have hzero : ∀ d, P.coeff d = 0 := by
      intro d
      exact abs_eq_zero.mp (le_antisymm ((hmax d).trans (le_of_not_gt hm)) (abs_nonneg _))
    exact hP (by ext d; simpa using hzero d)
  refine ⟨M⁻¹, inv_pos.mpr hM, ?_, j, ?_⟩
  · intro d
    simp only [coeff_C_mul, abs_mul, abs_inv, abs_of_pos hM]
    calc
      _ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hmax d) (inv_nonneg.mpr hM.le)
      _ = 1 := inv_mul_cancel₀ hM.ne'
  · simp only [coeff_C_mul, abs_mul, abs_inv, abs_of_pos hM]
    exact inv_mul_cancel₀ hM.ne'

theorem positive_scale_degree (P : MvPolynomial (Fin 14) ℝ) (t : ℝ)
    (hdeg : P.totalDegree ≤ 3) : (C t * P).totalDegree ≤ 3 := by
  exact (totalDegree_mul _ _).trans (by simpa using hdeg)

theorem positive_scale_sign (P : MvPolynomial (Fin 14) ℝ) (t : ℝ) (ht : 0 < t)
    (x : Fin 14 → ℝ) : 0 < eval x (C t * P) ↔ 0 < eval x P := by
  simp only [eval_mul, eval_C]
  exact mul_pos_iff_of_pos_left ht

end
end HeadComplexity.CubicNormalization
