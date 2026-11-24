import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

set_option linter.style.header false

/-!
Squarefree derivative interpolation at points whose last coordinates are fixed.
The factorization is exact and does not impose restrictions on the free points.
-/

noncomputable section
namespace HeadComplexity.CoordinateFlatJetRank
open Finset
open scoped BigOperators

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
  [DecidableEq ι] [DecidableEq κ]

def derivativeMatrix (u : κ → ℝ) (lam : η → ι → ℝ) :
    Matrix (Finset ι × Finset κ) (η × (ι ⊕ κ)) ℝ :=
  fun s hi => match hi.2 with
    | Sum.inl i => (if i ∈ s.1 then ∏ j ∈ s.1.erase i, lam hi.1 j else 0) *
        ∏ j ∈ s.2, u j
    | Sum.inr i => (∏ j ∈ s.1, lam hi.1 j) *
        if i ∈ s.2 then ∏ j ∈ s.2.erase i, u j else 0

def baseMatrix (u : κ → ℝ) :
    Matrix (Finset ι × Finset κ) (Finset ι × Option κ) ℝ :=
  fun s ti => if s.1 = ti.1 then match ti.2 with
    | none => ∏ j ∈ s.2, u j
    | some i => if i ∈ s.2 then ∏ j ∈ s.2.erase i, u j else 0
  else 0

def coefficientMatrix (lam : η → ι → ℝ) :
    Matrix (Finset ι × Option κ) (η × (ι ⊕ κ)) ℝ :=
  fun ti hi => match hi.2, ti.2 with
    | Sum.inl i, none => if i ∈ ti.1 then ∏ j ∈ ti.1.erase i, lam hi.1 j else 0
    | Sum.inr i, some j => if i = j then ∏ k ∈ ti.1, lam hi.1 k else 0
    | _, _ => 0

omit [Fintype η] in
theorem derivativeMatrix_factor (u : κ → ℝ) (lam : η → ι → ℝ) :
    derivativeMatrix u lam = baseMatrix u * coefficientMatrix lam := by
  classical
  ext s hi
  rcases hi with ⟨h, i⟩
  rcases i with i | i
  · simp [derivativeMatrix, Matrix.mul_apply, Fintype.sum_prod_type,
      Fintype.sum_option, baseMatrix, coefficientMatrix, mul_ite, ite_mul,
      sum_ite_eq, mul_comm]
  · simp [derivativeMatrix, Matrix.mul_apply, Fintype.sum_prod_type,
      Fintype.sum_option, baseMatrix, coefficientMatrix, mul_ite, ite_mul,
      sum_ite_eq, mul_comm]

theorem derivativeMatrix_rank_le (u : κ → ℝ) (lam : η → ι → ℝ) :
    (derivativeMatrix u lam).rank ≤ 2 ^ Fintype.card ι * (Fintype.card κ + 1) := by
  rw [derivativeMatrix_factor]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa [Fintype.card_option] using Matrix.rank_le_card_width (baseMatrix (ι := ι) u))

theorem derivativeMatrix_rank_le_sub_one (u : κ → ℝ) (lam : η → ι → ℝ) :
    (derivativeMatrix u lam).rank ≤
      2 ^ Fintype.card ι * (Fintype.card κ + 1) - 1 := by
  classical
  rw [derivativeMatrix_factor]
  apply (Matrix.rank_mul_le_right _ _).trans
  have hz : Function.support (coefficientMatrix (κ := κ) lam).row ⊆
      (univ.erase (∅, none) : Finset (Finset ι × Option κ)) := by
    rw [Function.support_subset_iff']
    intro ti hti
    have he : ti = (∅, none) := by simpa using hti
    subst ti
    ext hi
    rcases hi with ⟨h,i⟩
    rcases i with i | i <;> simp [Matrix.row, coefficientMatrix]
  have hr := Matrix.rank_le_card_of_support_subset (coefficientMatrix (κ := κ) lam)
    (univ.erase (∅, none)) hz
  simpa [Fintype.card_option] using hr

end HeadComplexity.CoordinateFlatJetRank
