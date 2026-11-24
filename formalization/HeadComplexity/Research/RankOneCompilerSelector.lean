import HeadComplexity.Research.BooleanPolynomialSupport
import HeadComplexity.Research.OneCoordinateMomentLift

set_option linter.style.header false

/-!
The polynomial selector obstruction used in a fixed rank-one kernel compiler.
The passage from a universal kernel identity to its isolated-direction selector
is a separate written argument; it is not assumed to hold for arbitrary
truth-table-preserving or data-dependent compilers.
-/
noncomputable section
namespace HeadComplexity.RankOneCompilerSelector
open Finset MvPolynomial
open scoped BigOperators

/-- A polynomial which is exactly a nonzero single-vertex indicator has degree
at least the Boolean dimension. -/
theorem dimension_le_of_vertex_selector {n d : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (v : Fin n → Bool)
    (hP : P.totalDegree ≤ d)
    (hsel : ∀ x, eval (cubePoint x) P = if x = v then 1 else 0) : n ≤ d := by
  classical
  have hs := BooleanPolynomialSupport.two_pow_le_degree_mul_support P hP
    (show ∃ x, eval (cubePoint x) P ≠ 0 from ⟨v, by simp [hsel]⟩)
  have hsupport : BooleanPolynomialSupport.supportSize
      (fun x => eval (cubePoint x) P) = 1 := by
    simp [BooleanPolynomialSupport.supportSize, hsel]
  rw [hsupport, mul_one] at hs
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hs

/-- A selector made from degree-r residues times degree-s factors cannot select
a single vertex in dimension greater than r+s. -/
theorem dimension_le_of_product_selector {n r s : ℕ} {J : Type*} [Fintype J]
    (L M : J → MvPolynomial (Fin n) ℝ) (v : Fin n → Bool)
    (hL : ∀ j, (L j).totalDegree ≤ r) (hM : ∀ j, (M j).totalDegree ≤ s)
    (hsel : ∀ x, ∑ j, eval (cubePoint x) (L j) * eval (cubePoint x) (M j) =
      if x = v then 1 else 0) : n ≤ r + s := by
  classical
  apply dimension_le_of_vertex_selector (∑ j, L j * M j) v
  · apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul (L j) (M j)).trans (Nat.add_le_add (hL j) (hM j))
  · intro x
    simpa using hsel x

/-- In particular, affine query residues times affine first moments cannot
produce an isolated-direction selector on three or more Boolean coordinates. -/
theorem no_affine_product_selector {n : ℕ} (hn : 3 ≤ n)
    {J : Type*} [Fintype J] (L M : J → MvPolynomial (Fin n) ℝ)
    (v : Fin n → Bool) (hL : ∀ j, (L j).totalDegree ≤ 1)
    (hM : ∀ j, (M j).totalDegree ≤ 1) :
    ¬ (∀ x, ∑ j, eval (cubePoint x) (L j) * eval (cubePoint x) (M j) =
      if x = v then 1 else 0) := by
  intro hs
  have := dimension_le_of_product_selector L M v hL hM hs
  omega

/-- The lower residue-degree threshold is attained in two coordinates by a
six-term scalar-kernel identity. The gate is affine in the second bit. -/
theorem two_bit_six_term_identity (F : ℝ → ℝ) (a b c : ℝ) (x y : Bool) :
    F (a + b * boolToReal x + c * boolToReal y) =
      (1 - boolToReal y) *
        (F a + F ((a + b) * boolToReal x) - F (a * boolToReal x)) +
      boolToReal y *
        (F (a + c) + F ((a + c + b) * boolToReal x) -
          F ((a + c) * boolToReal x)) := by
  cases x <;> cases y <;> simp [boolToReal, add_comm, add_left_comm, add_assoc]

end HeadComplexity.RankOneCompilerSelector
