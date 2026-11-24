import HeadComplexity.Polynomial.ParityThresholdDegree

set_option linter.style.header false

/-!
# Threshold degree under affine Boolean restrictions

The substitution lemma allows fixed coordinates, coordinate repetitions, and
coordinate complements. It applies to arbitrary real sign polynomials.
-/

namespace HeadComplexity

noncomputable section

open MvPolynomial Finset

theorem totalDegree_affine_substitution_le {n m : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (q : Fin n → MvPolynomial (Fin m) ℝ)
    (hq : ∀ i, (q i).totalDegree ≤ 1) :
    (eval₂Hom C q P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  apply totalDegree_finsetSum_le
  intro d hd
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd d.support (fun i ↦ q i ^ d i)).trans
  apply le_trans _ (le_totalDegree hd)
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hq i))

theorem ThresholdDegLE.affine_restriction {n m d : ℕ}
    {f : (Fin n → Bool) → Bool} (hf : ThresholdDegLE f d)
    (r : (Fin m → Bool) → Fin n → Bool)
    (q : Fin n → MvPolynomial (Fin m) ℝ)
    (hq : ∀ i, (q i).totalDegree ≤ 1)
    (he : ∀ x i, eval (cubePoint x) (q i) = boolToReal (r x i)) :
    ThresholdDegLE (fun x ↦ f (r x)) d := by
  obtain ⟨P, hP, hs⟩ := hf
  refine ⟨eval₂Hom C q P, (totalDegree_affine_substitution_le P q hq).trans hP, ?_⟩
  intro x
  change 0 < eval (cubePoint x) (eval₂ C q P) ↔ f (r x) = true
  rw [← eval_assoc]
  have hpoint : eval (cubePoint x) ∘ q = cubePoint (r x) := by
    funext i
    exact he x i
  rw [hpoint]
  exact hs (r x)

end

end HeadComplexity
