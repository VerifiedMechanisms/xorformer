import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Determinant of the six-coordinate generic cubic Hessian

The matrix below is the coordinate Hessian used for
`S₀ B₁ B₂ + S₁ B₀ B₂ + S₂ B₀ B₁`. Its determinant is independent of
the three S-coordinates and equals `-4 (B₀ B₁ B₂)^2`.
-/

namespace HeadComplexity.GenericCubicHessian

noncomputable section

open Matrix

def exchange (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fromBlocks 0 1 1 0

theorem det_exchange (n : ℕ) : (exchange n).det = (-1 : ℝ) ^ n := by
  let U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
    fromBlocks 1 1 0 1
  have hm : U * exchange n = fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) 1 1 0 := by
    simp [U, exchange, fromBlocks_multiply]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul] at hd
  simpa [U, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_one₁₁,
    Matrix.det_neg] using hd

theorem det_zero_corner {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℝ) :
    (fromBlocks (0 : Matrix (Fin n) (Fin n) ℝ) A Aᵀ L).det =
      (-1 : ℝ) ^ n * A.det ^ 2 := by
  have hm : fromBlocks A (0 : Matrix (Fin n) (Fin n) ℝ) L Aᵀ * exchange n =
      fromBlocks (0 : Matrix (Fin n) (Fin n) ℝ) A Aᵀ L := by
    simp [exchange, fromBlocks_multiply]
  rw [← hm, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, det_exchange,
    Matrix.det_transpose]
  ring

def offDiagonal (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, v 2, v 1; v 2, 0, v 0; v 1, v 0, 0]

theorem offDiagonal_transpose (v : Fin 3 → ℝ) :
    (offDiagonal v)ᵀ = offDiagonal v := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_offDiagonal (v : Fin 3 → ℝ) :
    (offDiagonal v).det = 2 * v 0 * v 1 * v 2 := by
  rw [Matrix.det_fin_three]
  simp [offDiagonal]
  ring

def hessian (s b : Fin 3 → ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fromBlocks 0 (offDiagonal b) (offDiagonal b)ᵀ (offDiagonal s)

def polynomial : MvPolynomial (Fin 3 ⊕ Fin 3) ℝ :=
  MvPolynomial.X (Sum.inl 0) * MvPolynomial.X (Sum.inr 1) * MvPolynomial.X (Sum.inr 2) +
    MvPolynomial.X (Sum.inl 1) * MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inr 2) +
    MvPolynomial.X (Sum.inl 2) * MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inr 1)

theorem polynomial_eval (s b : Fin 3 → ℝ) :
    MvPolynomial.eval (Sum.elim s b) polynomial =
      s 0 * b 1 * b 2 + s 1 * b 0 * b 2 + s 2 * b 0 * b 1 := by
  simp [polynomial]

theorem eval_second_pderiv (s b : Fin 3 → ℝ) (i j : Fin 3 ⊕ Fin 3) :
    MvPolynomial.eval (Sum.elim s b)
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j polynomial)) = hessian s b i j := by
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [polynomial, hessian, offDiagonal, Matrix.fromBlocks, Matrix.transpose_apply]

theorem hessian_symmetric (s b : Fin 3 → ℝ) : (hessian s b)ᵀ = hessian s b := by
  simp [hessian, Matrix.fromBlocks_transpose, offDiagonal_transpose]

theorem hessian_det (s b : Fin 3 → ℝ) :
    (hessian s b).det = -4 * (b 0 * b 1 * b 2) ^ 2 := by
  rw [hessian, det_zero_corner, det_offDiagonal]
  ring

theorem hessian_det_ne_zero (s b : Fin 3 → ℝ) (hb : ∀ i, b i ≠ 0) :
    (hessian s b).det ≠ 0 := by
  rw [hessian_det]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (hb 0) (hb 1)) (hb 2)))

theorem hessian_isUnit (s b : Fin 3 → ℝ) (hb : ∀ i, b i ≠ 0) :
    IsUnit (hessian s b) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (hessian_det_ne_zero s b hb)

theorem hessian_rank (s b : Fin 3 → ℝ) (hb : ∀ i, b i ≠ 0) :
    (hessian s b).rank = 6 := by
  simpa using Matrix.rank_of_isUnit (hessian s b) (hessian_isUnit s b hb)

theorem cross_hessian_det
    (U V : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) (s b : Fin 3 → ℝ) :
    (U * hessian s b * Vᵀ).det =
      -4 * U.det * V.det * (b 0 * b 1 * b 2) ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hessian_det]
  ring

theorem cross_hessian_det_ne_zero
    (U V : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ) (s b : Fin 3 → ℝ)
    (hU : U.det ≠ 0) (hV : V.det ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (U * hessian s b * Vᵀ).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero hU (hessian_det_ne_zero s b hb)) hV

end

end HeadComplexity.GenericCubicHessian
