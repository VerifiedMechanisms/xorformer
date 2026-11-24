import HeadComplexity.Polynomial.GenericPolynomialValues
import HeadComplexity.Polynomial.EvaluationDerivative
import HeadComplexity.Polynomial.RegularRootBound

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false

/-!
# Generic fibers of real polynomial maps

Generic values are regular and have a quantitative fiber bound. Algebraic
independence supplies the genericity, and diagonal perturbation supplies the
root count.
-/

namespace HeadComplexity.PolynomialRootCount

open MvPolynomial Set

/-- Regular values of a square real polynomial map form a dense set. -/
theorem dense_polynomial_regularValues {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) ℝ) :
    Dense {b : Fin n → ℝ | ∀ x, (∀ i, eval x (p i) = b i) →
      ∃ e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
        HasStrictFDerivAt (fun z i ↦ eval z (p i)) e.toContinuousLinearMap x} := by
  classical
  obtain ⟨F, hF, hpre⟩ := exists_countable_coefficient_field p
  choose q hq using hpre
  let : Countable F := hF
  have halg : algebraMap F ℝ = F.subtype := by ext; rfl
  apply (dense_algebraicIndependent F (Fin n)).mono
  intro b hb x hx
  have hval : (fun i ↦ aeval x (q i)) = b := by
    funext i
    rw [aeval_def, eval₂_eq_eval_map, halg]
    convert (congrArg (eval x) (hq i)).trans (hx i) using 1
  have hlin := linearIndependent_jacobian_of_values x q (hval.symm ▸ hb)
  have hjac : (fun j i ↦ aeval x (pderiv i (q j))) =
      (fun j i ↦ eval x (pderiv i (p j))) := by
    funext j i
    rw [← hq j, pderiv_map, aeval_def, eval₂_eq_eval_map, halg]
    rfl
  rw [hjac] at hlin
  obtain ⟨e, he⟩ := matrix_continuous_equiv _ hlin
  refine ⟨e, ?_⟩
  have h := hasStrictFDerivAt_pi.mpr (fun i ↦ hasStrictFDerivAt_eval (p i) x)
  convert h using 1
  ext y i
  rw [ContinuousLinearEquiv.coe_coe, he]
  simp [evalDerivative, Matrix.mulVec, dotProduct]

/-- On a dense set of values, every finite family in a fiber obeys the
quantitative root bound. -/
theorem dense_polynomial_boundedFibers {n d : ℕ}
    (p : Fin n → MvPolynomial (Fin n) ℝ) (hp : ∀ i, (p i).totalDegree ≤ d) :
    Dense {b : Fin n → ℝ | ∀ s : Finset (Fin n → ℝ),
      (∀ x ∈ s, ∀ i, eval x (p i) = b i) → s.card ≤ (d + 1) ^ n} := by
  classical
  apply (dense_polynomial_regularValues p).mono
  intro b hb s hs
  let q (i : Fin n) := p i - C (b i)
  have hq (i : Fin n) : (q i).totalDegree ≤ d :=
    (totalDegree_sub _ _).trans (max_le (hp i) (by simp))
  have hz (x : s) (i : Fin n) : eval (x : Fin n → ℝ) (q i) = 0 := by
    simp [q, hs x x.2 i]
  choose e he using fun x : s ↦ hb (x : Fin n → ℝ) (hs x x.2)
  have heq (x : s) : HasStrictFDerivAt (fun z i ↦ eval z (q i))
      (e x).toContinuousLinearMap (x : Fin n → ℝ) := by
    convert (he x).sub_const b using 1
    funext z i
    simp [q]
  simpa using regular_roots_card_le q hq (fun x : s ↦ (x : Fin n → ℝ))
    Subtype.val_injective hz e heq

end HeadComplexity.PolynomialRootCount
