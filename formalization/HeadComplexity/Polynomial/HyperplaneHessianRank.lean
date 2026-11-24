import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Hessian rank under a rank-one projection

A codimension-one compression removes at most two matrix ranks. The Hessian
of a product of three linear forms has rank at most three. These are exact,
nonquantitative parts of the pure RoPE cubic pole obstruction.
-/

namespace HeadComplexity.HyperplaneHessianRank
noncomputable section
open scoped BigOperators Matrix

/-- Subadditivity of finite matrix rank over the reals. -/
theorem rank_add_le {ι κ : Type*} [Finite ι] [Fintype κ]
    (A B : Matrix ι κ ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  letI := Fintype.ofFinite ι
  rw [Matrix.rank, Matrix.mulVecLin_add, Matrix.rank, Matrix.rank]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Removing a rank-one part on each side loses at most two ranks.
No idempotence or symmetry assumptions are needed. -/
theorem rank_compression {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (v d : ι → ℝ) :
    M.rank ≤ ((1 - Matrix.vecMulVec v d)ᵀ * M *
      (1 - Matrix.vecMulVec v d)).rank + 2 := by
  let Q := Matrix.vecMulVec v d
  let P : Matrix ι ι ℝ := 1 - Q
  have he : M = Pᵀ * M * P + Qᵀ * M + Pᵀ * M * Q := by
    dsimp only [P]
    simp only [Matrix.transpose_sub, Matrix.transpose_one, sub_mul, mul_sub,
      one_mul, mul_one]
    abel
  have h1 : (Qᵀ * M).rank ≤ 1 := by
    exact (Matrix.rank_mul_le_left _ _).trans (by
      simpa [Q, Matrix.transpose_vecMulVec] using Matrix.rank_vecMulVec_le d v)
  have h2 : (Pᵀ * M * Q).rank ≤ 1 :=
    (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_vecMulVec_le v d)
  have h := rank_add_le (Pᵀ * M * P + Qᵀ * M) (Pᵀ * M * Q)
  have h' := rank_add_le (Pᵀ * M * P) (Qᵀ * M)
  rw [← he] at h
  change M.rank ≤ (Pᵀ * M * P).rank + 2
  omega

/-- The six-term Hessian of the product of three linear forms.
Here `a`, `b`, and `c` are their values at the evaluation point. -/
def tripleHessian {ι : Type*} (u v w : ι → ℝ) (a b c : ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ c * (u i * v j + v i * u j) +
    b * (u i * w j + w i * u j) + a * (v i * w j + w i * v j)

/-- All Hessian columns lie in the span of the three coefficient vectors. -/
theorem tripleHessian_rank_le {ι : Type*} [Fintype ι]
    (u v w : ι → ℝ) (a b c : ℝ) : (tripleHessian u v w a b c).rank ≤ 3 := by
  let V : Matrix ι (Fin 3) ℝ := fun i ↦ ![u i, v i, w i]
  let T : Matrix (Fin 3) ι ℝ := ![fun j ↦ c * v j + b * w j,
    fun j ↦ c * u j + a * w j, fun j ↦ b * u j + a * v j]
  have he : tripleHessian u v w a b c = V * T := by
    ext i j
    simp [tripleHessian, Matrix.mul_apply, Fin.sum_univ_succ, V, T]
    ring
  rw [he]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width V)

/-- A homogeneous linear polynomial with its coefficient vector. -/
def linear {ι : Type*} [Fintype ι] (u : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (u i) * MvPolynomial.X i

@[simp] theorem pderiv_linear {ι : Type*} [Fintype ι] (u : ι → ℝ) (i : ι) :
    MvPolynomial.pderiv i (linear u) = MvPolynomial.C (u i) := by
  classical
  simp [linear, MvPolynomial.pderiv_X, Pi.single_apply, mul_ite]

/-- This matrix is the actual polynomial Hessian, evaluated at any point. -/
theorem eval_product_hessian {ι : Type*} [Fintype ι]
    (u v w z : ι → ℝ) (i j : ι) :
    MvPolynomial.eval z (MvPolynomial.pderiv i (MvPolynomial.pderiv j
      (linear u * linear v * linear w))) =
      tripleHessian u v w (MvPolynomial.eval z (linear u))
        (MvPolynomial.eval z (linear v)) (MvPolynomial.eval z (linear w)) i j := by
  simp [tripleHessian]
  ring

/-- A matrix of rank at least six cannot compress to a three-factor Hessian. -/
theorem compression_ne_tripleHessian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (v d u₀ u₁ u₂ : ι → ℝ) (a b c : ℝ)
    (hM : 6 ≤ M.rank) :
    (1 - Matrix.vecMulVec v d)ᵀ * M * (1 - Matrix.vecMulVec v d) ≠
      tripleHessian u₀ u₁ u₂ a b c := by
  intro he
  have hc := rank_compression M v d
  rw [he] at hc
  have ht := tripleHessian_rank_le u₀ u₁ u₂ a b c
  omega

end
end HeadComplexity.HyperplaneHessianRank
