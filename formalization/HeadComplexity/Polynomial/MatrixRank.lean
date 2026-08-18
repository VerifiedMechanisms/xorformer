import Mathlib.LinearAlgebra.Matrix.Rank

set_option linter.style.header false

/-!
# Finite matrix-rank bounds

The natural-number matrix rank API supplies outer-product bounds but does not
package the two elementary subadditivity statements needed by partition-rank
arguments.  This file provides those reusable lemmas.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

namespace Matrix

variable {K m n ι : Type*} [Field K] [Fintype n]

/-- Natural-number matrix rank is subadditive. -/
theorem rank_add_le (A B : Matrix m n K) :
    (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank]
  have hrange :
      LinearMap.range (A + B).mulVecLin ≤
        LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro y ⟨x, rfl⟩
    change (A + B).mulVec x ∈
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin
    rw [Matrix.add_mulVec]
    apply Submodule.add_mem_sup
    · exact ⟨x, rfl⟩
    · exact ⟨x, rfl⟩
  exact (Submodule.finrank_mono hrange).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- The rank of a sum over a finite set is at most the sum of the ranks. -/
theorem rank_finset_sum_le (s : Finset ι) (A : ι → Matrix m n K) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (rank_add_le (A i) (∑ j ∈ s, A j)).trans
        (Nat.add_le_add_left ih _)

/-- The rank of a finite sum is at most the sum of the ranks. -/
theorem rank_sum_le [Fintype ι] (A : ι → Matrix m n K) :
    (∑ i, A i).rank ≤ ∑ i, (A i).rank := by
  simpa using rank_finset_sum_le (Finset.univ : Finset ι) A

/-- A sum of `N` outer products has rank at most `N`. -/
theorem rank_sum_vecMulVec_le [Fintype ι]
    (u : ι → m → K) (v : ι → n → K) :
    (∑ i, Matrix.vecMulVec (u i) (v i)).rank ≤ Fintype.card ι := by
  refine (rank_sum_le fun i ↦ Matrix.vecMulVec (u i) (v i)).trans ?_
  calc
    (∑ i, (Matrix.vecMulVec (u i) (v i)).rank) ≤ ∑ _ : ι, 1 :=
      Finset.sum_le_sum fun i _ ↦ Matrix.rank_vecMulVec_le (u i) (v i)
    _ = Fintype.card ι := by simp

end Matrix

end HeadComplexity
