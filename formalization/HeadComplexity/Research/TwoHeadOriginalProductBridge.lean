import HeadComplexity.Research.TwoHeadProductCompilation
import HeadComplexity.Atoms.ClearedNormalForm

set_option linter.style.header false

/-!
An original two-head computation, including weak negative labels and arbitrary
permitted embedding dimension, admits three affine-times-exponential terms.
All five polynomial forms in the conclusion have degree at most one. The
exponential of an affine Boolean form is a positive product of one-bit factors.
No assertion about arbitrary head counts or the requested lower bound is made.
-/

noncomputable section

namespace HeadComplexity.TwoHeadOriginalProductBridge

open MvPolynomial Finset
open scoped BigOperators

private lemma degree_scalar_mul {n : ℕ} (a : ℝ)
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ 1) :
    (C a * P).totalDegree ≤ 1 := by
  exact (totalDegree_mul _ _).trans (by simpa using hP)

theorem original_two_heads_have_three_affine_exponential_terms {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : computableWithHeadsN n 2 f) :
    ∃ P Q R U V : MvPolynomial (Fin n) ℝ,
      P.totalDegree ≤ 1 ∧ Q.totalDegree ≤ 1 ∧ R.totalDegree ≤ 1 ∧
      U.totalDegree ≤ 1 ∧ V.totalDegree ≤ 1 ∧
      ∀ x, if f x then
        0 < eval (cubePoint x) P * Real.exp (eval (cubePoint x) U) +
          eval (cubePoint x) Q * Real.exp (eval (cubePoint x) V) + eval (cubePoint x) R
      else
        eval (cubePoint x) P * Real.exp (eval (cubePoint x) U) +
          eval (cubePoint x) Q * Real.exp (eval (cubePoint x) V) + eval (cubePoint x) R < 0 := by
  obtain ⟨φ, c, hφ⟩ := exists_strict_fracCertificate (fracComputable_of_computable hf)
  let A := (φ 0).numPoly
  let D := (φ 1).numPoly
  let B := (φ 0).denPoly
  let E := (φ 1).denPoly
  let av := fun x => eval (cubePoint x) A
  let dv := fun x => eval (cubePoint x) D
  let bv := fun x => eval (cubePoint x) B
  let ev := fun x => eval (cubePoint x) E
  have hscore : ∀ x, c + av x / bv x + dv x / ev x = c + ∑ h, (φ h).eval x := by
    intro x
    simp [av, dv, bv, ev, A, D, B, E, FracAtom.eval_eq_numPoly_div_denPoly,
      Fin.sum_univ_succ, add_assoc]
  have hstrict : ∀ x, c + av x / bv x + dv x / ev x ≠ 0 := by
    intro x
    rw [hscore]
    have hs := hφ x
    cases hx : f x <;> simp only [hx, Bool.false_eq_true, ↓reduceIte] at hs
    · exact ne_of_lt hs
    · exact ne_of_gt hs
  obtain ⟨ε, hε, hc⟩ := TwoHeadProductCompilation.uniform_two_head_sign_compilation
    av dv bv ev c (fun x => (φ 0).denPoly_pos x)
      (fun x => (φ 1).denPoly_pos x) hstrict
  let t := ε/2
  have ht : 0 < t := half_pos hε
  have hte : t < ε := half_lt_self hε
  let P := A + C c * B
  let R := -(P+D)
  have hP : P.totalDegree ≤ 1 := (totalDegree_add _ _).trans
    (max_le (φ 0).numPoly_totalDegree_le (degree_scalar_mul c B (φ 0).denPoly_totalDegree_le))
  have hD : D.totalDegree ≤ 1 := (φ 1).numPoly_totalDegree_le
  have hR : R.totalDegree ≤ 1 := by
    dsimp [R]
    rw [totalDegree_neg]
    exact (totalDegree_add _ _).trans (max_le hP hD)
  refine ⟨P, D, R, C t * E, C t * B, hP, hD, hR,
    degree_scalar_mul t E (φ 1).denPoly_totalDegree_le,
    degree_scalar_mul t B (φ 0).denPoly_totalDegree_le, ?_⟩
  intro x
  have hp := hc t ht hte x
  have heq : eval (cubePoint x) P * Real.exp (eval (cubePoint x) (C t * E)) +
      eval (cubePoint x) D * Real.exp (eval (cubePoint x) (C t * B)) + eval (cubePoint x) R =
      TwoHeadProductCompilation.compiled (av x+c*bv x) (dv x) (bv x) (ev x) t := by
    simp [P, R, av, dv, bv, ev, TwoHeadProductCompilation.compiled]
    ring
  rw [heq]
  have hs := hφ x
  rw [← hscore] at hs
  cases hx : f x <;> simp only [hx, Bool.false_eq_true, ↓reduceIte] at hs ⊢
  · exact (mul_pos_iff.mp hp).resolve_left (fun h => (not_lt_of_ge (le_of_lt hs)) h.1) |>.2
  · exact (mul_pos_iff.mp hp).resolve_right (fun h => (not_lt_of_ge (le_of_lt hs)) h.1) |>.2

#print axioms original_two_heads_have_three_affine_exponential_terms

end HeadComplexity.TwoHeadOriginalProductBridge
