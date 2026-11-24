import HeadComplexity.Polynomial.ThreeHeadPoleHessian
import HeadComplexity.Polynomial.PureCubicChart

set_option linter.style.header false

/-!
# The explicit fourteen-variable target has no oriented raw cubic representation

This instantiates the general pole-Hessian theorem with the exact rational
coefficients used in the finite Boolean construction. It is an equality
obstruction for raw polynomials, not by itself the Boolean lower bound.
-/

namespace HeadComplexity.ExplicitCubicRawObstruction
noncomputable section
open scoped BigOperators Matrix
open PureRoPEReplication GenericCubicHessianPullback

def firstSix : Fin 3 ⊕ Fin 3 → Fin 14 :=
  Sum.elim (fun h ↦ ⟨h.val, by omega⟩) (fun h ↦ ⟨h.val + 3, by omega⟩)

def firstMinor : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  (slopes baseS baseB).submatrix firstSix id

def firstMinorInverse : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fun i j ↦ PureCubicChart.chartInverse (firstSix j) (firstSix i)

set_option maxHeartbeats 4000000 in
-- Check all 36 entries of the rational inverse without external computation.
theorem firstMinor_mul_inverse : firstMinor * firstMinorInverse = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [firstMinor, firstMinorInverse, firstSix, slopes, baseS, baseB,
      PureCubicChart.chartInverse, PureCubicChart.inverseNumerator,
      Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply,
      Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.ext_iff] <;> decide

theorem firstMinor_det_ne_zero : firstMinor.det ≠ 0 := by
  have hd := congrArg Matrix.det firstMinor_mul_inverse
  rw [Matrix.det_mul, Matrix.det_one] at hd
  intro hz
  rw [hz, zero_mul] at hd
  norm_num at hd

theorem baseB_mixed : ∀ h, ∃ i j, 0 < baseB h i ∧ baseB h j < 0 := by
  intro h
  refine ⟨13, 0, ?_⟩
  fin_cases h <;> norm_num [baseB]

/-- No unrestricted numerator choices and uniformly oriented denominator
choices can equal the concrete homogeneous cubic used in the separation. -/
theorem cubic_ne_oriented (N E : Fin 3 → Fin 14 → ℝ)
    (hE : ∀ h, (∀ i, 0 < E h i) ∨ (∀ i, E h i < 0) ∨ E h = 0) :
    cubic baseS baseB ≠ cubic N E :=
  ThreeHeadPoleHessian.mixed_independent_cubic_ne_oriented
    baseS baseB firstSix firstMinor_det_ne_zero baseB_mixed N E hE

/-- The same exclusion includes a free homogeneous readout contribution. -/
theorem cubic_ne_oriented_with_readout (N E : Fin 3 → Fin 14 → ℝ) (c : ℝ)
    (hE : ∀ h, (∀ i, 0 < E h i) ∨ (∀ i, E h i < 0) ∨ E h = 0) :
    cubic baseS baseB ≠ cubic N E + MvPolynomial.C c * linearPolynomial (E 0) *
      linearPolynomial (E 1) * linearPolynomial (E 2) := by
  rw [cubic_add_readout]
  exact cubic_ne_oriented _ E hE

end
end HeadComplexity.ExplicitCubicRawObstruction
