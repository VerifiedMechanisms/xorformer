import HeadComplexity.Polynomial.CubicDerivativeTensor
import HeadComplexity.Polynomial.QuantitativeCubicRecovery
import HeadComplexity.Polynomial.ExplicitCubicGapConstants

set_option linter.style.header false

/-!
# An explicit squarefree coefficient gap against every oriented three-head cubic

This combines rank-six recovery, actual third derivatives, exact Vandermonde
cross minors, and the denominator-pole obstruction. All competing linear forms
and readout coefficients are unrestricted real parameters.
-/

namespace HeadComplexity.ExplicitCubicSquarefreeGap
noncomputable section
open scoped BigOperators
open MvPolynomial GenericCubicHessianPullback PureRoPEReplication
open CubicDerivativeTensor QuantitativeCubicRecovery ExplicitCubicVandermonde
open ExplicitCubicGapConstants ExplicitCubicRawGap

theorem target_tensor_bound (i j k : Fin 14) :
    |tensor (cubic baseS baseB) i j k| ≤ 18 := by
  apply cubic_tensor_abs_le_eighteen
  · intro h i
    exact ExplicitCubicQuantitativeBounds.slopes_abs_le_one i (Sum.inl h)
  · intro h i
    exact ExplicitCubicQuantitativeBounds.slopes_abs_le_one i (Sum.inr h)

theorem target_cross_lower : CrossLower (tensor (cubic baseS baseB)) crossGap := by
  intro i k hik
  obtain ⟨a, b, hav, hab, hd⟩ := exists_cross_lower i k hik
  refine ⟨a, b, hav, hab, ?_⟩
  rw [slice_eq_hessian _ (cubic_homogeneous _ _)]
  exact hd

/-- Uniform exclusion in a distinct-variable ordinary coefficient. The
orientation alternatives include constant denominators via the zero vector. -/
theorem squarefree_coefficient_gap (N E : Fin 3 → Fin 14 → ℝ)
    (hE : ∀ h, (∀ i, 0 < E h i) ∨ (∀ i, E h i < 0) ∨ E h = 0) :
    ∃ i j k : Fin 14, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ squarefreeRadius <
      |coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1)
          (cubic baseS baseB) -
        coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1)
          (cubic N E)| := by
  by_contra hn
  push Not at hn
  have hs (i j k : Fin 14) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      |tensor (cubic baseS baseB) i j k - tensor (cubic N E) i j k| ≤ squarefreeRadius := by
    rw [tensor_squarefree _ _ _ _ hij hik hjk, tensor_squarefree _ _ _ _ hij hik hjk]
    exact hn i j k hij hik hjk
  have ht := all_entries_error_bound
    (tensor (cubic baseS baseB)) (tensor (cubic N E)) crossGap squarefreeRadius
    crossGap_pos squarefreeRadius_pos.le squarefreeRadius_le_one determinant_perturbation_small
    (tensor_symmetric _) (tensor_symmetric _)
    (cubic_tensor_rank_le_six _ _) (cubic_tensor_rank_le_six _ _) target_cross_lower
    (fun i j k _ _ _ ↦ target_tensor_bound i j k)
    (fun i k _ ↦ (target_tensor_bound i i k).trans (by norm_num)) hs first_recovery_small
  have hK : 0 ≤ QuantitativeCrossRecovery.inverseBound crossGap :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (QuantitativeCrossRecovery.inverseBound_ge_one crossGap crossGap_pos)
  have hr : 0 ≤ squarefreeRadius := squarefreeRadius_pos.le
  have hc := coefficient_difference_le_of_tensor
    (cubic baseS baseB) (cubic N E) (cubic_homogeneous _ _) (cubic_homogeneous _ _)
    (10 ^ 10 * QuantitativeCrossRecovery.inverseBound crossGap ^ 3 * squarefreeRadius)
    (by positivity) ht
  obtain ⟨d, hd⟩ := raw_coefficient_gap N E hE
  exact (not_lt_of_ge (hc d)) (total_recovery_lt_raw_gap.trans hd)

/-- The same gap includes an arbitrary cubic readout product. -/
theorem squarefree_coefficient_gap_with_readout
    (N E : Fin 3 → Fin 14 → ℝ) (c : ℝ)
    (hE : ∀ h, (∀ i, 0 < E h i) ∨ (∀ i, E h i < 0) ∨ E h = 0) :
    ∃ i j k : Fin 14, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ squarefreeRadius <
      |coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1)
          (cubic baseS baseB) -
        coeff (Finsupp.single k 1 + Finsupp.single i 1 + Finsupp.single j 1)
          (cubic N E + C c * linearPolynomial (E 0) * linearPolynomial (E 1) *
            linearPolynomial (E 2))| := by
  rw [cubic_add_readout]
  exact squarefree_coefficient_gap _ E hE

end
end HeadComplexity.ExplicitCubicSquarefreeGap
