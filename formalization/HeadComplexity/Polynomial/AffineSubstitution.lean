import HeadComplexity.Results.AffineFreeSparsity

set_option linter.style.header false

/-!
# Affine Boolean substitutions

Polynomial threshold degree is monotone under substitutions whose coordinates
have affine real interpolants. This includes variable identification and
individual input complementation, without asserting either operation preserves
attention denominator orientation.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n m d : ℕ}

/-- Substitute affine coordinate polynomials into a squarefree polynomial. -/
noncomputable def SquarefreePolynomial.substitute
    (P : SquarefreePolynomial n) (q : Fin n → MvPolynomial (Fin m) ℝ) :
    MvPolynomial (Fin m) ℝ :=
  ∑ S : Finset (Fin n), C (P.coeff S) * ∏ i ∈ S, q i

theorem SquarefreePolynomial.substitute_totalDegree_le
    (P : SquarefreePolynomial n) (hP : P.DegreeLE d)
    (q : Fin n → MvPolynomial (Fin m) ℝ) (hq : ∀ i, (q i).totalDegree ≤ 1) :
    (P.substitute q).totalDegree ≤ d := by
  classical
  apply totalDegree_finsetSum_le
  intro S _
  by_cases hc : P.coeff S = 0
  · simp [hc]
  · have hp : (∏ i ∈ S, q i).totalDegree ≤ S.card := by
      exact (totalDegree_finsetProd S q).trans
        ((Finset.sum_le_sum fun i _ ↦ hq i).trans_eq (by simp))
    exact (totalDegree_mul _ _).trans (by simpa using hp.trans (hP S hc))

theorem SquarefreePolynomial.substitute_eval
    (P : SquarefreePolynomial n) (q : Fin n → MvPolynomial (Fin m) ℝ)
    (g : (Fin m → Bool) → (Fin n → Bool))
    (hq : ∀ x i, MvPolynomial.eval (cubePoint x) (q i) = boolToReal (g x i))
    (x : Fin m → Bool) :
    MvPolynomial.eval (cubePoint x) (P.substitute q) = P.eval (g x) := by
  classical
  rw [substitute, map_sum, ← P.fullSum_eq_eval]
  apply Finset.sum_congr rfl
  intro S _
  simp only [map_mul, eval_C, map_prod, hq, squarefreeMonomial]

/-- Affine identification of input coordinates cannot increase threshold degree. -/
theorem ThresholdDegLE.affineSubstitution
    {f : (Fin n → Bool) → Bool} (hf : ThresholdDegLE f d)
    (g : (Fin m → Bool) → (Fin n → Bool))
    (q : Fin n → MvPolynomial (Fin m) ℝ)
    (hqdeg : ∀ i, (q i).totalDegree ≤ 1)
    (hqeval : ∀ x i, eval (cubePoint x) (q i) = boolToReal (g x i)) :
    ThresholdDegLE (fun x ↦ f (g x)) d := by
  obtain ⟨P, hPdeg, hP⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE hf
  refine ⟨P.substitute q, P.substitute_totalDegree_le hPdeg q hqdeg, fun x ↦ ?_⟩
  rw [P.substitute_eval q g hqeval x]
  exact (hP (g x)).1

end HeadComplexity
