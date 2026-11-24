import HeadComplexity.Polynomial.PureCubicFiniteKernel
import HeadComplexity.Polynomial.GenericCubicHessianPullback

set_option linter.style.header false

/-! # The finite rational zero-chart kernel in the original fourteen coordinates -/

namespace HeadComplexity.PureCubicRawKernel

noncomputable section

open MvPolynomial Matrix PureCubicChart PureCubicIrreducible PureCubicFiniteKernel
open GenericCubicHessianPullback PureRoPEReplication
open scoped BigOperators

def linearSubstitution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  aeval (fun i ↦ linearPolynomial (M i))

theorem linear_degree {n : ℕ} (a : Fin n → ℝ) :
    (linearPolynomial a).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  simpa using totalDegree_mul (C (a i)) (X i)

theorem substitution_degree {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (P : MvPolynomial (Fin n) ℝ) :
    (linearSubstitution M P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  have hm : (linearSubstitution M (monomial d (P.coeff d))).totalDegree ≤
      d.sum (fun _ e ↦ e) := by
    simp only [linearSubstitution, aeval_monomial, algebraMap_eq, Finsupp.prod]
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    apply (totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (totalDegree_pow _ _).trans
      (by simpa using Nat.mul_le_mul_left (d i) (linear_degree (M i)))
  exact hm.trans (le_totalDegree hd)

theorem eval_substitution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (P : MvPolynomial (Fin n) ℝ) (z : Fin n → ℝ) :
    eval z (linearSubstitution M P) = eval (M *ᵥ z) P := by
  change aeval z (aeval (fun i ↦ linearPolynomial (M i)) P) = aeval (M *ᵥ z) P
  rw [comp_aeval_apply]
  congr 2
  funext i
  simp [linearPolynomial, Matrix.mulVec, dotProduct]

theorem substitution_comp {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) :
    (linearSubstitution N).comp (linearSubstitution M) = linearSubstitution (M * N) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, linearSubstitution, aeval_X, linearPolynomial,
    map_sum, map_mul, aeval_C, algebraMap_eq]
  simp only [Matrix.mul_apply, map_sum, map_mul]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem substitution_one {n : ℕ} :
    linearSubstitution (1 : Matrix (Fin n) (Fin n) ℝ) = AlgHom.id ℝ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [linearSubstitution, linearPolynomial, Matrix.one_apply]

theorem substitution_inverse {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ)
    (hMN : M * N = 1) (P : MvPolynomial (Fin n) ℝ) :
    linearSubstitution N (linearSubstitution M P) = P := by
  change ((linearSubstitution N).comp (linearSubstitution M)) P = P
  rw [substitution_comp, hMN, substitution_one]
  rfl

/-- The actual unshifted cleared polynomial, expressed in the fourteen mean variables. -/
def rawTarget : MvPolynomial (Fin 14) ℝ :=
  linearSubstitution chart coordinatePolynomial

def rawNode (y : Fin 13 → ℝ) : Fin 14 → ℝ := chartInverse *ᵥ graphPoint y

theorem rawTarget_formula : rawTarget =
    linearPolynomial (baseS 0) * (1 + linearPolynomial (baseB 1)) *
      (1 + linearPolynomial (baseB 2)) +
    linearPolynomial (baseS 1) * (1 + linearPolynomial (baseB 0)) *
      (1 + linearPolynomial (baseB 2)) +
    linearPolynomial (baseS 2) * (1 + linearPolynomial (baseB 0)) *
      (1 + linearPolynomial (baseB 1)) := by
  simp [rawTarget, linearSubstitution, coordinatePolynomial, chart]

theorem eval_rawTarget (z : Fin 14 → ℝ) :
    eval z rawTarget =
      (∑ i, baseS 0 i * z i) * (1 + ∑ i, baseB 1 i * z i) *
        (1 + ∑ i, baseB 2 i * z i) +
      (∑ i, baseS 1 i * z i) * (1 + ∑ i, baseB 0 i * z i) *
        (1 + ∑ i, baseB 2 i * z i) +
      (∑ i, baseS 2 i * z i) * (1 + ∑ i, baseB 0 i * z i) *
        (1 + ∑ i, baseB 1 i * z i) := by
  rw [rawTarget_formula]
  simp [linearValue]

theorem rawTarget_degree : rawTarget.totalDegree = 3 := by
  apply le_antisymm
  · exact (substitution_degree chart coordinatePolynomial).trans coordinatePolynomial_degree.le
  · have hi := substitution_inverse chart chartInverse chart_mul_inverse coordinatePolynomial
    have hd := substitution_degree chartInverse rawTarget
    rw [show linearSubstitution chartInverse rawTarget = coordinatePolynomial from hi,
      coordinatePolynomial_degree] at hd
    exact hd

theorem finite_raw_kernel (Q : MvPolynomial (Fin 14) ℝ) (hQ : Q.totalDegree ≤ 3)
    (hzero : ∀ y : Fin 13 → ℝ, (∀ i, y i ∈ PureCubicGraph.chartGrid) →
      eval (rawNode y) Q = 0) :
    ∃ c : ℝ, Q = C c * rawTarget := by
  obtain ⟨c, hc⟩ := finite_chart_kernel (linearSubstitution chartInverse Q)
    ((substitution_degree chartInverse Q).trans hQ) (by
      intro y hy
      rw [eval_substitution]
      exact hzero y hy)
  refine ⟨c, ?_⟩
  have he := congrArg (linearSubstitution chart) hc
  rw [substitution_inverse chartInverse chart chart_inverse_mul] at he
  simpa [rawTarget, linearSubstitution] using he

theorem eval_rawTarget_means {m : ℕ} (x : Fin (14 * m) → Bool) :
    eval (means x) rawTarget = clearedScore 0 x := by
  rw [eval_rawTarget]
  simp [clearedScore, ThreeHeadCubicFace.cleared, numerator, denominator]

theorem rawNode_zero (y : Fin 13 → ℝ)
    (hy : ∀ i, y i ∈ PureCubicGraph.chartGrid) : eval (rawNode y) rawTarget = 0 := by
  rw [rawTarget, eval_substitution, rawNode, chart_apply_inverse]
  exact eval_target_graphPoint y (grid_leading_positive y hy).ne'

theorem finite_raw_kernel_iff (Q : MvPolynomial (Fin 14) ℝ) (hQ : Q.totalDegree ≤ 3) :
    (∀ y : Fin 13 → ℝ, (∀ i, y i ∈ PureCubicGraph.chartGrid) →
      eval (rawNode y) Q = 0) ↔ ∃ c : ℝ, Q = C c * rawTarget := by
  constructor
  · exact finite_raw_kernel Q hQ
  · rintro ⟨c, rfl⟩ y hy
    simp [rawNode_zero y hy]

end
end HeadComplexity.PureCubicRawKernel
