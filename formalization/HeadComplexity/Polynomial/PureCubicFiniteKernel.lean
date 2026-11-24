import HeadComplexity.Polynomial.PureCubicGraphKernel
import HeadComplexity.Polynomial.PureCubicGraph

set_option linter.style.header false

/-!
# The finite ten-point chart has exactly the cubic scalar kernel

Denominator clearing turns restriction of any cubic to the rational graph into
a thirteen-variable polynomial of degree at most nine. Exact ten-point product
interpolation and primitive graph division therefore identify its full kernel.
-/

namespace HeadComplexity.PureCubicFiniteKernel

noncomputable section

open MvPolynomial PureCubicGraphKernel PureCubicIrreducible
open scoped BigOperators

def clearedGraph (Q : MvPolynomial (Fin 14) ℝ) : CoefficientRing :=
  ∑ k : Fin 4, (split Q).coeff k.val * (-trailing) ^ k.val * leading ^ (3 - k.val)

theorem leading_degree : leading.totalDegree ≤ 2 := by
  have h₃ := totalDegree_add (1 : CoefficientRing) (X 3)
  have h₄ := totalDegree_add (1 : CoefficientRing) (X 4)
  have h := totalDegree_mul (1 + X 3 : CoefficientRing) (1 + X 4)
  simp only [totalDegree_one, totalDegree_X] at *
  unfold leading
  omega

theorem trailing_degree : trailing.totalDegree ≤ 3 := by
  have hl (i : Fin 13) : (1 + X i : CoefficientRing).totalDegree ≤ 1 := by
    simpa using totalDegree_add (1 : CoefficientRing) (X i)
  have ht (i j k : Fin 13) :
      (X i * (1 + X j) * (1 + X k) : CoefficientRing).totalDegree ≤ 3 := by
    have h₁ := totalDegree_mul (X i : CoefficientRing) (1 + X j)
    have h₂ := totalDegree_mul (X i * (1 + X j) : CoefficientRing) (1 + X k)
    have hj := hl j
    have hk := hl k
    simp only [totalDegree_X] at h₁
    omega
  have h := totalDegree_add (X 0 * (1 + X 2) * (1 + X 4) : CoefficientRing)
    (X 1 * (1 + X 2) * (1 + X 3))
  have ha := ht 0 2 4
  have hb := ht 1 2 3
  unfold trailing
  omega

theorem split_degree_le (Q : MvPolynomial (Fin 14) ℝ) (hQ : Q.totalDegree ≤ 3) :
    (split Q).natDegree ≤ 3 := by
  change (finSuccEquiv ℝ 13 Q).natDegree ≤ 3
  rw [natDegree_finSuccEquiv]
  exact (degreeOf_le_totalDegree Q 0).trans hQ

theorem clearedGraph_degree (Q : MvPolynomial (Fin 14) ℝ) (hQ : Q.totalDegree ≤ 3) :
    (clearedGraph Q).totalDegree ≤ 9 := by
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro k _
  by_cases hc : (split Q).coeff k.val = 0
  · simp [hc]
  · have hcoeff := totalDegree_coeff_finSuccEquiv_add_le Q k.val hc
    change ((split Q).coeff k.val).totalDegree + k.val ≤ Q.totalDegree at hcoeff
    have h₁ := totalDegree_mul ((split Q).coeff k.val) ((-trailing) ^ k.val)
    have h₂ := totalDegree_mul ((split Q).coeff k.val * (-trailing) ^ k.val)
      (leading ^ (3 - k.val))
    have ht := (totalDegree_pow (-trailing) k.val).trans
      (Nat.mul_le_mul_left k.val (show (-trailing).totalDegree ≤ 3 by
        simpa using trailing_degree))
    have hl := (totalDegree_pow leading (3 - k.val)).trans
      (Nat.mul_le_mul_left (3 - k.val) leading_degree)
    have hk := k.isLt
    omega

theorem cubic_evaluation {R K : Type*} [CommRing R] [Field K]
    (p : Polynomial R) (hp : p.natDegree ≤ 3) (φ : R →+* K) (r : K) :
    (p.map φ).eval r = φ (p.coeff 0) + φ (p.coeff 1) * r +
      φ (p.coeff 2) * r ^ 2 + φ (p.coeff 3) * r ^ 3 := by
  have he := congrArg (fun q : Polynomial R ↦ (q.map φ).eval r)
    (p.as_sum_range' 4 (by omega))
  simpa [Finset.sum_range_succ] using he

theorem clearedGraph_identity {K : Type*} [Field K]
    (Q : MvPolynomial (Fin 14) ℝ) (hQ : Q.totalDegree ≤ 3)
    (φ : CoefficientRing →+* K) (hA : φ leading ≠ 0) :
    φ (clearedGraph Q) = (φ leading) ^ 3 *
      ((split Q).map φ).eval (-(φ trailing) / φ leading) := by
  rw [cubic_evaluation _ (split_degree_le Q hQ)]
  simp [clearedGraph, Fin.sum_univ_succ, map_add, map_mul, map_pow, map_neg]
  field_simp
  ring

theorem clearedGraph_zero_iff (Q : MvPolynomial (Fin 14) ℝ) (hQ : Q.totalDegree ≤ 3) :
    clearedGraph Q = 0 ↔ restriction Q = 0 := by
  let φ := algebraMap CoefficientRing RationalFunctions
  have hA : φ leading ≠ 0 := by
    intro h
    apply leading_ne_zero
    exact (IsFractionRing.injective CoefficientRing RationalFunctions) (by simpa [φ] using h)
  have he := clearedGraph_identity Q hQ φ hA
  change φ (clearedGraph Q) = (φ leading) ^ 3 * restriction Q at he
  constructor
  · intro hz
    rw [hz, map_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hA)
  · intro hz
    rw [hz, mul_zero] at he
    exact (IsFractionRing.injective CoefficientRing RationalFunctions) (by simpa [φ] using he)

def graphPoint (y : Fin 13 → ℝ) : Fin 14 → ℝ :=
  Fin.cons (-eval y trailing / eval y leading) y

theorem graphPoint_first (y : Fin 13 → ℝ)
    (h₁ : 1 + y 3 ≠ 0) (h₂ : 1 + y 4 ≠ 0) :
    graphPoint y 0 = PureCubicGraph.graphFirst (y 0) (y 1) (y 2) (y 3) (y 4) := by
  simp only [graphPoint, Fin.cons_zero, leading, trailing, map_mul, map_add,
    map_one, eval_X, PureCubicGraph.graphFirst]
  field_simp
  ring

@[simp] theorem graphPoint_succ (y : Fin 13 → ℝ) (i : Fin 13) :
    graphPoint y i.succ = y i := by rfl

theorem eval_clearedGraph (Q : MvPolynomial (Fin 14) ℝ) (hQ : Q.totalDegree ≤ 3)
    (y : Fin 13 → ℝ) (hA : eval y leading ≠ 0) :
    eval y (clearedGraph Q) = (eval y leading) ^ 3 * eval (graphPoint y) Q := by
  rw [clearedGraph_identity Q hQ (eval y) hA]
  rw [graphPoint, eval_eq_eval_mv_eval']
  rfl

theorem grid_leading_positive (y : Fin 13 → ℝ)
    (hy : ∀ i, y i ∈ PureCubicGraph.chartGrid) : 0 < eval y leading := by
  have h₃ := PureCubicGraph.chartGrid_nonnegative (hy 3)
  have h₄ := PureCubicGraph.chartGrid_nonnegative (hy 4)
  simp only [leading, map_mul, map_add, map_one, eval_X]
  positivity

/-- Exact rank-kernel certificate for all ten-to-the-thirteen rational graph points. -/
theorem finite_chart_kernel (Q : MvPolynomial (Fin 14) ℝ) (hQ : Q.totalDegree ≤ 3)
    (hzero : ∀ y : Fin 13 → ℝ, (∀ i, y i ∈ PureCubicGraph.chartGrid) →
      eval (graphPoint y) Q = 0) :
    ∃ c : ℝ, Q = C c * coordinatePolynomial := by
  have hclear : clearedGraph Q = 0 := by
    apply PureCubicGraph.eq_zero_of_chartGrid _ (clearedGraph_degree Q hQ)
    intro y hy
    rw [eval_clearedGraph Q hQ y (grid_leading_positive y hy).ne', hzero y hy, mul_zero]
  exact (degree_three_kernel Q hQ).mp ((clearedGraph_zero_iff Q hQ).mp hclear)

theorem eval_target_graphPoint (y : Fin 13 → ℝ) (hA : eval y leading ≠ 0) :
    eval (graphPoint y) coordinatePolynomial = 0 := by
  have hclear : clearedGraph coordinatePolynomial = 0 :=
    (clearedGraph_zero_iff coordinatePolynomial coordinatePolynomial_degree.le).mpr
      restriction_target
  have h := eval_clearedGraph coordinatePolynomial coordinatePolynomial_degree.le y hA
  rw [hclear, map_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hA)

theorem finite_chart_kernel_iff (Q : MvPolynomial (Fin 14) ℝ)
    (hQ : Q.totalDegree ≤ 3) :
    (∀ y : Fin 13 → ℝ, (∀ i, y i ∈ PureCubicGraph.chartGrid) →
      eval (graphPoint y) Q = 0) ↔ ∃ c : ℝ, Q = C c * coordinatePolynomial := by
  constructor
  · exact finite_chart_kernel Q hQ
  · rintro ⟨c, rfl⟩ y hy
    simp only [map_mul, eval_C, eval_target_graphPoint y (grid_leading_positive y hy).ne',
      mul_zero]

end

end HeadComplexity.PureCubicFiniteKernel
