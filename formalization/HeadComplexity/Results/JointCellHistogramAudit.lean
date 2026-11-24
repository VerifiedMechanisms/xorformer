import HeadComplexity.Results.JointCellLabelAudit
import HeadComplexity.Results.JointFamilyScalarCapacity

set_option linter.style.header false

/-! Finite-alphabet checks for exact tensor corrections. These declarations
concern Cauchy fibers and histogram marginals, not unrestricted joint heads. -/

namespace HeadComplexity.AxisZeroGluing

open scoped BigOperators

private theorem histogram_cauchy_product_degree {q : ℕ}
    (pole : Fin q → ℝ) (S : Finset (Fin q)) :
    (∏ i ∈ S, (Polynomial.C (pole i) - Polynomial.X : Polynomial ℝ)).natDegree ≤
      S.card := by
  refine (Polynomial.natDegree_prod_le S _).trans ?_
  calc
    (∑ i ∈ S, (Polynomial.C (pole i) - Polynomial.X : Polynomial ℝ).natDegree) ≤
        ∑ _i ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    _ = S.card := by simp

/-- A nonzero `q`-pole Cauchy fiber cannot vanish at `q` distinct exterior
tokens. In particular, a tensor correction cannot annihilate a larger finite
word alphabet merely by choosing the residues of that fiber. -/
theorem jointCell_cauchy_zero_fiber_coefficients {q Q : ℕ}
    (pole : Fin q → ℝ) (token : Fin Q → ℝ)
    (hpole : Function.Injective pole) (htoken : Function.Injective token)
    (hsep : ∀ i j, pole i - token j ≠ 0) (hqQ : q ≤ Q)
    (η : Fin q → ℝ)
    (hzero : ∀ j, ∑ i, η i / (pole i - token j) = 0) :
    ∀ i, η i = 0 := by
  classical
  by_cases hq : q = 0
  · subst q
    exact fun i ↦ Fin.elim0 i
  let P := jointFamilyCauchyPolynomial Finset.univ pole η 0
  have hPdef : P = ∑ i : Fin q, Polynomial.C (η i) *
      ∏ k ∈ Finset.univ.erase i, (Polynomial.C (pole k) - Polynomial.X) := by
    simp [P, jointFamilyCauchyPolynomial]
  have hdeg : P.natDegree ≤ q - 1 := by
    rw [hPdef]
    apply (Polynomial.natDegree_sum_le _ _).trans
    apply Finset.sup_le
    intro i _
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    simpa using histogram_cauchy_product_degree pole (Finset.univ.erase i)
  have hPeval (j : Fin Q) : P.eval (token j) = 0 := by
    dsimp [P]
    rw [jointFamilyCauchyPolynomial_eval]
    · simp [hzero]
    · exact fun i _ ↦ hsep i j
  have hP : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    htoken hPeval (by simpa using hdeg.trans_lt (show q - 1 < Q by omega))
  intro i
  have hev : P.eval (pole i) = η i * ∏ k ∈ Finset.univ.erase i, (pole k - pole i) := by
    rw [hPdef]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hi : i ∈ (Finset.univ : Finset (Fin q)).erase j := by simp [Ne.symm hji]
      have hz : (∏ k ∈ Finset.univ.erase j, (pole k - pole i)) = 0 :=
        Finset.prod_eq_zero hi (sub_self _)
      rw [hz, mul_zero]
    · simp
  have hprod : (∏ k ∈ Finset.univ.erase i, (pole k - pole i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (fun h ↦ (Finset.mem_erase.mp hk).1 (hpole h))
  rw [hP, Polynomial.eval_zero] at hev
  exact (mul_eq_zero.mp hev.symm).resolve_right hprod

/-- Sampling at as many distinct exterior nodes as histogram bins determines
the entire Cauchy histogram. Coefficients may be arbitrary real numbers. -/
theorem jointCell_cauchy_histogram_injective {q Q : ℕ}
    (pole : Fin q → ℝ) (token : Fin Q → ℝ)
    (hpole : Function.Injective pole) (htoken : Function.Injective token)
    (hsep : ∀ i j, pole i - token j ≠ 0) (hqQ : q ≤ Q)
    (u v : Fin q → ℝ)
    (heq : ∀ j, (∑ i, u i / (pole i - token j)) =
      ∑ i, v i / (pole i - token j)) : u = v := by
  have hz := jointCell_cauchy_zero_fiber_coefficients pole token hpole htoken hsep hqQ
    (fun i ↦ u i - v i) (fun j ↦ by
      simp only [sub_div, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (heq j))
  funext i
  exact sub_eq_zero.mp (hz i)

/-- Two binary-digit histograms can have the same separate digit marginals
while their Cauchy aggregates differ. The diagonal and off-diagonal tables
each contain one occurrence of each value of either digit. -/
theorem jointCell_binary_marginals_do_not_determine_cauchy {d u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hbudget : u + v < d) :
    1 / (d - u) + 1 / (d - v) < 1 / d + 1 / (d - u - v) := by
  have h := audited_cauchy_weight_two_defect_pos hu hv hbudget
  linarith

end HeadComplexity.AxisZeroGluing
