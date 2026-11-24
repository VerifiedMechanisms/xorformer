import HeadComplexity.Polynomial.CubicMonomialBasis
import HeadComplexity.Polynomial.PureCubicNodeBounds
import HeadComplexity.Polynomial.FiniteKernelMinor

set_option linter.style.header false

/-! # Quantitative coefficient recovery from the actual finite cubic zero chart -/

namespace HeadComplexity.PureCubicInterpolation

noncomputable section

open MvPolynomial Matrix CubicMonomialBasis PureCubicRawKernel PureCubicNodeBounds
open scoped BigOperators

abbrev Rows := Fin 13 → Fin 10

def evaluationMatrix : Matrix Rows (Fin 680) ℝ := fun y j ↦
  (exponent j).prod (fun i k ↦ rawNode (indexedGrid y) i ^ k)

def coefficients (P : MvPolynomial (Fin 14) ℝ) : Fin 680 → ℝ :=
  fun j ↦ P.coeff (exponent j)

theorem evaluation_polynomial (q : Fin 680 → ℝ) (y : Rows) :
    (evaluationMatrix *ᵥ q) y = eval (rawNode (indexedGrid y)) (polynomial q) := by
  simp only [evaluationMatrix, Matrix.mulVec, dotProduct, polynomial, map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem evaluation_coefficients (P : MvPolynomial (Fin 14) ℝ) (hP : P.totalDegree ≤ 3)
    (y : Rows) :
    (evaluationMatrix *ᵥ coefficients P) y = eval (rawNode (indexedGrid y)) P := by
  rw [evaluation_polynomial]
  change eval _ (polynomial (fun j ↦ P.coeff (exponent j))) = _
  rw [polynomial_reconstruct P hP]

theorem target_kernel : evaluationMatrix *ᵥ coefficients rawTarget = 0 := by
  ext y
  rw [evaluation_coefficients rawTarget rawTarget_degree.le]
  exact rawNode_zero _ (indexedGrid_mem y)

theorem matrix_kernel (q : Fin 680 → ℝ) (hq : evaluationMatrix *ᵥ q = 0) :
    ∃ c : ℝ, q = c • coefficients rawTarget := by
  obtain ⟨c, hc⟩ := finite_raw_kernel (polynomial q) (polynomial_degree q) (by
    intro y hy
    choose j hj using fun i ↦ Finset.mem_image.mp (hy i)
    have he : y = indexedGrid j := by funext i; exact (hj i).2.symm
    rw [he, ← evaluation_polynomial, hq]
    rfl)
  refine ⟨c, ?_⟩
  funext j
  have he := congrArg (coeff (exponent j)) hc
  simpa only [polynomial_coefficient, coeff_C_mul, Pi.smul_apply, smul_eq_mul,
    coefficients] using he

theorem target_coefficient_nonzero : ∃ j, coefficients rawTarget j ≠ 0 := by
  by_contra h
  push Not at h
  have he : coefficients rawTarget = 0 := funext h
  have hp : polynomial (coefficients rawTarget) = 0 := by simp [he, polynomial]
  change polynomial (fun j ↦ rawTarget.coeff (exponent j)) = 0 at hp
  rw [polynomial_reconstruct rawTarget rawTarget_degree.le] at hp
  have hd := rawTarget_degree
  rw [hp, totalDegree_zero] at hd
  omega

/-- Every cubic whose values are small at all actual chart nodes is uniformly
close in all 680 coefficients to a scalar multiple of the explicit raw target. -/
theorem coefficient_recovery (Q : MvPolynomial (Fin 14) ℝ)
    (hQ : Q.totalDegree ≤ 3) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ∀ y : Fin 13 → ℝ, (∀ i, y i ∈ PureCubicGraph.chartGrid) →
      |eval (rawNode y) Q| ≤ ε) :
    ∃ c : ℝ, ∀ d : Fin 14 →₀ ℕ,
      |Q.coeff d - c * rawTarget.coeff d| < (2 : ℝ) ^ 300000 * ε := by
  have hrows (y : Rows) := finite_cubic_row (indexedGrid y) (indexedGrid_mem y)
  choose q hq hqb hqi using hrows
  let K : Matrix Rows (Fin 680) ℤ := fun y j ↦
    Classical.choose (hqi y (exponent j) (exponent_degree j))
  have hrow (y : Rows) (j : Fin 680) :
      q y * evaluationMatrix y j = (K y j : ℝ) :=
    Classical.choose_spec (hqi y (exponent j) (exponent_degree j))
  obtain ⟨j, hj⟩ := target_coefficient_nonzero
  obtain ⟨c, hc⟩ := FiniteKernelMinor.quantitative_kernel_recovery
    evaluationMatrix (coefficients rawTarget) (coefficients Q) j hj target_kernel matrix_kernel
    K q (fun y j ↦ node_monomial_bound _ (indexedGrid_mem y) (exponent j)) hq
    (fun y ↦ (hqb y).le) hrow ε hε (by
      intro y
      rw [evaluation_coefficients Q hQ]
      exact hsmall _ (indexedGrid_mem y))
  refine ⟨c, ?_⟩
  intro d
  by_cases hd : d.sum (fun _ k ↦ k) ≤ 3
  · obtain ⟨j, rfl⟩ := exponent_surjective d hd
    exact hc j
  · have hd' : 3 < ∑ i ∈ d.support, d i := Nat.lt_of_not_ge hd
    have h₁ : Q.coeff d = 0 := coeff_eq_zero_of_totalDegree_lt (hQ.trans_lt hd')
    have h₂ : rawTarget.coeff d = 0 :=
      coeff_eq_zero_of_totalDegree_lt (rawTarget_degree.le.trans_lt hd')
    rw [h₁, h₂, mul_zero, sub_zero, abs_zero]
    exact mul_pos (pow_pos (by norm_num) _) hε

end
end HeadComplexity.PureCubicInterpolation
