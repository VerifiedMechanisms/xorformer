import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Recover every matrix entry from an invertible cross block

This is the exact Schur identity used to recover repeated-index cubic
coefficients from squarefree coefficients when every Hessian has rank at most six.
-/

namespace HeadComplexity.LowRankCrossRecovery
noncomputable section
open scoped BigOperators Matrix

/-- No disjointness is needed for the matrix identity. Applications choose
cross rows and columns disjoint so their entries are squarefree coefficients. -/
theorem entry_of_rank_le {r : ℕ} {ι κ : Type*} [Fintype κ]
    (M : Matrix ι κ ℝ) (a : Fin r → ι) (b : Fin r → κ)
    (hrank : M.rank ≤ r) (hdet : (M.submatrix a b).det ≠ 0) (i : ι) (j : κ) :
    M i j = ∑ p, ∑ q, M i (b p) * (M.submatrix a b)⁻¹ p q * M (a q) j := by
  classical
  let A := M.submatrix a b
  let B : Matrix (Fin r) Unit ℝ := fun p _ ↦ M (a p) j
  let C : Matrix Unit (Fin r) ℝ := fun _ p ↦ M i (b p)
  let D : Matrix Unit Unit ℝ := fun _ _ ↦ M i j
  let T := Matrix.fromBlocks A B C D
  have hsub : T = M.submatrix (Sum.elim a (fun _ : Unit ↦ i))
      (Sum.elim b (fun _ : Unit ↦ j)) := by
    ext x y
    cases x <;> cases y <;> rfl
  have hTrank : T.rank ≤ r := by
    rw [hsub]
    exact (Matrix.rank_submatrix_le M _ _).trans hrank
  have hTdet : T.det = 0 := by
    by_contra h
    have hu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr h)
    have hc := Matrix.rank_of_isUnit T hu
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at hc
    omega
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hdet)
  have he : T.det = A.det * (M i j - (C * A⁻¹ * B) () ()) := by
    dsimp only [T]
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv,
      Matrix.det_unique (D - C * A⁻¹ * B)]
    rfl
  have hz : M i j - (C * A⁻¹ * B) () () = 0 := by
    rw [hTdet] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hdet
  have hi := sub_eq_zero.mp hz
  rw [hi]
  simp only [Matrix.mul_apply, Finset.sum_mul, C, B, A]
  rw [Finset.sum_comm]

/-- Equality of the cross block and the two bordering vectors determines an entry. -/
theorem entry_eq_of_cross_data {r : ℕ} {ι κ : Type*} [Fintype κ]
    (M N : Matrix ι κ ℝ) (a : Fin r → ι) (b : Fin r → κ)
    (hM : M.rank ≤ r) (hN : N.rank ≤ r) (hdet : (M.submatrix a b).det ≠ 0)
    (i : ι) (j : κ)
    (hcross : ∀ p q, M (a p) (b q) = N (a p) (b q))
    (hrow : ∀ p, M i (b p) = N i (b p))
    (hcol : ∀ q, M (a q) j = N (a q) j) : M i j = N i j := by
  have hA : M.submatrix a b = N.submatrix a b := by ext p q; exact hcross p q
  have hdetN : (N.submatrix a b).det ≠ 0 := by rw [← hA]; exact hdet
  rw [entry_of_rank_le M a b hM hdet i j,
    entry_of_rank_le N a b hN hdetN i j]
  simp only [hA, hrow, hcol]

/-- The diagonal version used at each coordinate Hessian. -/
theorem diagonal_of_rank_six {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (a b : Fin 6 → ι)
    (hrank : M.rank ≤ 6) (hdet : (M.submatrix a b).det ≠ 0) (i : ι) :
    M i i = ∑ p, ∑ q, M i (b p) * (M.submatrix a b)⁻¹ p q * M (a q) i :=
  entry_of_rank_le M a b hrank hdet i i

end
end HeadComplexity.LowRankCrossRecovery
