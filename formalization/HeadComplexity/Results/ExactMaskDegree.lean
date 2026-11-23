import HeadComplexity.Polynomial.FreshBit
import HeadComplexity.Atoms.ClearedNormalForm

set_option linter.style.header false

/-!
# Exact singleton masks require full polynomial degree

The degree-lowering difference of two Boolean slices proves that a polynomial
whose cube evaluations are supported at the zero vertex has degree at least
the number of coordinates. Applying this to a cleared affine-ratio score
gives the corresponding head lower bound for an exact singleton mask.
The Hamming-ball extension by restriction to a maximal support vertex is
written in `artifacts/head-compression/exponent-literature.tex`.
-/

namespace HeadComplexity

open MvPolynomial
open scoped BigOperators

/-- Exact localization at one cube vertex, unlike sign representation of its
indicator, requires full polynomial degree. -/
theorem le_totalDegree_of_cube_supported_at_zero
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hnonzero : eval (cubePoint (fun _ ↦ false)) P ≠ 0)
    (hvanish : ∀ x : Fin n → Bool, x ≠ (fun _ ↦ false) →
      eval (cubePoint x) P = 0) :
    n ≤ P.totalDegree := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hfalse : consBit false (fun _ : Fin n ↦ false) =
          (fun _ : Fin (n + 1) ↦ false) := by
        funext i
        exact Fin.cases (by simp) (fun j ↦ by simp) i
      have htrue : consBit true (fun _ : Fin n ↦ false) ≠
          (fun _ : Fin (n + 1) ↦ false) := by
        intro h
        have := congrFun h 0
        simp at this
      have hpositive : 0 < P.totalDegree := by
        by_contra hn
        have hz : P.totalDegree = 0 := by omega
        have hconst := totalDegree_eq_zero_iff_eq_C.mp hz
        have hv := hvanish _ htrue
        rw [hconst] at hnonzero hv
        simp only [eval_C] at hnonzero hv
        exact hnonzero hv
      have hDnonzero : eval (cubePoint (fun _ : Fin n ↦ false))
          (freshDifferencePolynomial P) ≠ 0 := by
        rw [freshDifferencePolynomial_eval, hvanish _ htrue, hfalse, zero_sub]
        exact neg_ne_zero.mpr hnonzero
      have hDvanish : ∀ x : Fin n → Bool, x ≠ (fun _ ↦ false) →
          eval (cubePoint x) (freshDifferencePolynomial P) = 0 := by
        intro x hx
        have hcons (z : Bool) : consBit z x ≠
            (fun _ : Fin (n + 1) ↦ false) := by
          intro heq
          apply hx
          funext i
          have hi := congrFun heq i.succ
          simpa using hi
        rw [freshDifferencePolynomial_eval,
          hvanish _ (hcons true), hvanish _ (hcons false), sub_self]
      have hdegree := (ih (freshDifferencePolynomial P) hDnonzero hDvanish).trans
        (freshDifferencePolynomial_totalDegree_le P)
      omega

/-- An exact singleton mask in the cleared positive-affine-ratio model needs
at least one head per cube coordinate. This is an exact-zero support result,
not a lower bound for the sign representation of the singleton indicator. -/
theorem le_heads_of_clearedAffinePoly_supported_at_zero
    {n H : ℕ} (A : AffineFractionFamily n H) (c : ℝ)
    (hnonzero : eval (cubePoint (fun _ ↦ false)) (clearedAffinePoly A c) ≠ 0)
    (hvanish : ∀ x : Fin n → Bool, x ≠ (fun _ ↦ false) →
      eval (cubePoint x) (clearedAffinePoly A c) = 0) :
    n ≤ H :=
  (le_totalDegree_of_cube_supported_at_zero _ hnonzero hvanish).trans
    (clearedAffinePoly_totalDegree_le A c)

/-- The exact singleton obstruction directly for the repository's admissible
atoms. All denominator positivity hypotheses are supplied by `FracAtom`. -/
theorem le_heads_of_atom_score_supported_at_zero
    {n H : ℕ} (φ : Fin H → FracAtom n) (c : ℝ)
    (hnonzero : c + ∑ h, (φ h).eval (fun _ ↦ false) ≠ 0)
    (hvanish : ∀ x : Fin n → Bool, x ≠ (fun _ ↦ false) →
      c + ∑ h, (φ h).eval x = 0) :
    n ≤ H := by
  have hpnonzero : eval (cubePoint (fun _ ↦ false)) (clearedAtomPoly φ c) ≠ 0 := by
    rw [clearedAtomPoly_eval]
    exact mul_ne_zero (atomDenProduct_eval_pos φ _).ne' hnonzero
  have hpvanish : ∀ x : Fin n → Bool, x ≠ (fun _ ↦ false) →
      eval (cubePoint x) (clearedAtomPoly φ c) = 0 := by
    intro x hx
    rw [clearedAtomPoly_eval, hvanish x hx, mul_zero]
  exact (le_totalDegree_of_cube_supported_at_zero _ hpnonzero hpvanish).trans
    (clearedAtomPoly_totalDegree_le φ c)

end HeadComplexity
