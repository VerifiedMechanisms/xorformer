import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Closedness of the finite-rank upper strata

These generic topological facts supply the closed relation needed by the
arbitrary-head compact-frame theorem. They make no assumptions about bounded
factorization parameters.
-/

namespace HeadComplexity.RoPEClosedRank

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]

theorem isClosed_finrank_range_le (k : ℕ) :
    IsClosed {L : E →L[ℝ] F | Module.finrank ℝ (LinearMap.range L.toLinearMap) ≤ k} := by
  have ho := isOpen_setOf_nat_le_rank (𝕜 := ℝ) (E := E) (F := F) (k + 1)
  convert ho.isClosed_compl using 1
  ext L
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
  rw [LinearMap.rank, ← Module.finrank_eq_rank]
  norm_cast
  omega

noncomputable def matrixMap {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    Matrix m n ℝ ≃ₗ[ℝ] ((n → ℝ) →L[ℝ] (m → ℝ)) :=
  Matrix.toLin'.trans LinearMap.toContinuousLinearMap

theorem continuous_matrixMap {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    Continuous (matrixMap (m := m) (n := n)) :=
  (matrixMap (m := m) (n := n)).toLinearMap.continuous_of_finiteDimensional

theorem isClosed_matrix_rank_le {m n : Type*} [Finite m] [Fintype n]
    (k : ℕ) : IsClosed {A : Matrix m n ℝ | A.rank ≤ k} := by
  classical
  letI := Fintype.ofFinite m
  have hc := (isClosed_finrank_range_le (E := n → ℝ) (F := m → ℝ) k).preimage
    (continuous_matrixMap (m := m) (n := n))
  exact hc

theorem matrix_rank_le_of_tendsto {m n : Type*} [Finite m] [Fintype n]
    (k : ℕ) (A : ℕ → Matrix m n ℝ) (B : Matrix m n ℝ)
    (hA : Filter.Tendsto A Filter.atTop (nhds B)) (hrank : ∀ j, (A j).rank ≤ k) :
    B.rank ≤ k :=
  (isClosed_matrix_rank_le k).mem_of_tendsto hA (Filter.Eventually.of_forall hrank)

end HeadComplexity.RoPEClosedRank
