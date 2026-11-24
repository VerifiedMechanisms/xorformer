import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

set_option linter.style.header false

/-!
An exact rank obstruction for squarefree derivative interpolation.  Positive
points varying in one coordinate can have arbitrarily many distinct parameters
while their full derivative matrix has rank at most twice the ambient dimension.
This is not a head-complexity lower bound or a margin-repair theorem.
-/

noncomputable section
namespace HeadComplexity.CoordinateLineJetRank
open Finset
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

def point (j : ι) (u : ι → ℝ) (lam : κ → ℝ) (h : κ) (i : ι) : ℝ :=
  if i = j then lam h else u i

def derivativeMatrix (c : κ → ι → ℝ) : Matrix (Finset ι) (κ × ι) ℝ :=
  fun s hi => if hi.2 ∈ s then ∏ k ∈ s.erase hi.2, c hi.1 k else 0

def baseMatrix (j : ι) (u : ι → ℝ) : Matrix (Finset ι) (Bool × ι) ℝ :=
  fun s bi => if bi.2 ∈ s then
    if j ∈ s.erase bi.2 then
      if bi.1 then ∏ k ∈ (s.erase bi.2).erase j, u k else 0
    else
      if bi.1 then 0 else ∏ k ∈ s.erase bi.2, u k
  else 0

def coefficientMatrix (lam : κ → ℝ) : Matrix (Bool × ι) (κ × ι) ℝ :=
  fun bi hi => if bi.2 = hi.2 then if bi.1 then lam hi.1 else 1 else 0

omit [Fintype ι] [Fintype κ] in
theorem point_pos (j : ι) (u : ι → ℝ) (lam : κ → ℝ)
    (hu : ∀ i, 0 < u i) (hlam : ∀ h, 0 < lam h) :
    ∀ h i, 0 < point j u lam h i := by
  intro h i
  simp only [point]
  split_ifs
  · exact hlam h
  · exact hu i

omit [Fintype κ] in
theorem derivativeMatrix_factor (j : ι) (u : ι → ℝ) (lam : κ → ℝ) :
    derivativeMatrix (point j u lam) = baseMatrix j u * coefficientMatrix lam := by
  classical
  ext s hi
  rcases hi with ⟨h,i⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    coefficientMatrix, baseMatrix, derivativeMatrix]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  by_cases his : i ∈ s
  · simp only [his, ↓reduceIte]
    by_cases hj : j ∈ s.erase i
    · simp only [hj, ↓reduceIte, add_zero]
      rw [← Finset.mul_prod_erase (s.erase i) (point j u lam h) hj]
      simp only [point, ↓reduceIte]
      rw [mul_comm]
      congr 1
      apply prod_congr rfl
      intro k hk
      simp only [mem_erase] at hk
      simp [hk.1]
    · simp only [hj, ↓reduceIte, zero_mul, zero_add]
      apply prod_congr rfl
      intro k hk
      simp [point, show k ≠ j by intro he; subst k; exact hj hk]
  · simp [his]

theorem derivativeMatrix_rank_le (j : ι) (u : ι → ℝ) (lam : κ → ℝ) :
    (derivativeMatrix (point j u lam)).rank ≤ 2 * Fintype.card ι := by
  rw [derivativeMatrix_factor]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width (baseMatrix j u))

theorem derivativeMatrix_rank_le_sub_one (j : ι) (u : ι → ℝ) (lam : κ → ℝ) :
    (derivativeMatrix (point j u lam)).rank ≤ 2 * Fintype.card ι - 1 := by
  classical
  rw [derivativeMatrix_factor]
  apply (Matrix.rank_mul_le_left _ _).trans
  have hz : Function.support (baseMatrix j u).transpose.row ⊆
      (univ.erase (true,j) : Finset (Bool × ι)) := by
    rw [Function.support_subset_iff']
    intro bi hbi
    have he : bi = (true,j) := by simpa using hbi
    subst bi
    ext s
    simp [Matrix.row, baseMatrix]
  have hr := Matrix.rank_le_card_of_support_subset (baseMatrix j u).transpose
    (univ.erase (true,j)) hz
  simpa [Matrix.rank_transpose] using hr

omit [Fintype ι] [Fintype κ] in
theorem point_injective (j : ι) (u : ι → ℝ) (lam : κ → ℝ)
    (hlam : Function.Injective lam) : Function.Injective (point j u lam) := by
  intro a b hab
  apply hlam
  have ht := congrFun hab j
  simpa [point] using ht

end HeadComplexity.CoordinateLineJetRank
