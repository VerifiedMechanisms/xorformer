import HeadComplexity.Polynomial.MatrixRank
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Sign rank of finite Boolean matrices

This module defines the natural-number sign-rank used by partition lower
bounds.  A representing real matrix must be strictly positive on true entries
and strictly negative on false entries.
-/

namespace HeadComplexity

variable {α β : Type*}

/-- A real matrix realizes a Boolean matrix with strict signs. -/
def StrictSignMatrix (M : Matrix α β ℝ) (f : α → β → Bool) : Prop :=
  ∀ i j, if f i j then 0 < M i j else M i j < 0

/-- The canonical `±1` realization of a Boolean matrix. -/
noncomputable def booleanSignMatrix (f : α → β → Bool) : Matrix α β ℝ :=
  fun i j ↦ if f i j then 1 else -1

theorem booleanSignMatrix_strict (f : α → β → Bool) :
    StrictSignMatrix (booleanSignMatrix f) f := by
  intro i j
  cases h : f i j <;> simp [booleanSignMatrix, h]

private theorem exists_signRankBound [Fintype β] (f : α → β → Bool) :
    ∃ r : ℕ, ∃ M : Matrix α β ℝ, StrictSignMatrix M f ∧ M.rank ≤ r :=
  ⟨(booleanSignMatrix f).rank,
    booleanSignMatrix f, booleanSignMatrix_strict f, le_rfl⟩

/-- Sign rank is the least natural rank bound of a strict real realization. -/
noncomputable def signRank [Fintype β] (f : α → β → Bool) : ℕ := by
  classical
  exact Nat.find (exists_signRankBound f)

/-- The minimum sign-rank bound is attained by a strict matrix. -/
theorem signRank_spec [Fintype β] (f : α → β → Bool) :
    ∃ M : Matrix α β ℝ, StrictSignMatrix M f ∧ M.rank ≤ signRank f := by
  classical
  exact Nat.find_spec (exists_signRankBound f)

/-- Every strict realization upper-bounds sign rank. -/
theorem signRank_le_of_strict [Fintype β]
    {f : α → β → Bool} {M : Matrix α β ℝ}
    (hM : StrictSignMatrix M f) : signRank f ≤ M.rank := by
  classical
  exact Nat.find_min' (exists_signRankBound f) ⟨M, hM, le_rfl⟩

/-- An attaining matrix can be chosen with rank exactly the sign rank. -/
theorem exists_strictSignMatrix_rank_eq [Fintype β] (f : α → β → Bool) :
    ∃ M : Matrix α β ℝ, StrictSignMatrix M f ∧ M.rank = signRank f := by
  obtain ⟨M, hstrict, hrank⟩ := signRank_spec f
  exact ⟨M, hstrict,
    Nat.le_antisymm hrank (signRank_le_of_strict hstrict)⟩

/-- Sign rank is bounded by the smaller matrix dimension. -/
theorem signRank_le_min_card [Fintype α] [Fintype β] (f : α → β → Bool) :
    signRank f ≤ min (Fintype.card α) (Fintype.card β) := by
  apply le_min
  · exact (signRank_le_of_strict (booleanSignMatrix_strict f)).trans
      (Matrix.rank_le_card_height _)
  · exact (signRank_le_of_strict (booleanSignMatrix_strict f)).trans
      (Matrix.rank_le_card_width _)

end HeadComplexity
