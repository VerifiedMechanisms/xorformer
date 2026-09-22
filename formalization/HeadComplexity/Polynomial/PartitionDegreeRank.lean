import HeadComplexity.Polynomial.PartitionPolynomial
import HeadComplexity.Polynomial.UnivariateReduction
import Mathlib.Data.Nat.Choose.Sum

set_option linter.style.header false

/-!
# Degree-side partition-rank bounds

On the Boolean cube, an arbitrary monomial depends only on its support.  After
grouping all monomials with the same support on one side of a coordinate
partition, each group is one outer product.  A degree-`H` polynomial therefore
has partition rank at most the number of subsets of size at most `H` on either
side.
-/

namespace HeadComplexity

open Finset MvPolynomial
open scoped BigOperators

variable {n : ℕ} {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Coordinates set to true for a Boolean assignment on an arbitrary finite
index type. -/
def trueSet (x : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i ↦ x i = true

omit [DecidableEq ι] in
@[simp] theorem mem_trueSet {x : ι → Bool} {i : ι} :
    i ∈ trueSet x ↔ x i = true := by
  simp [trueSet]

/-- Support of a monomial on the left side of a partition. -/
def partitionLeftSupport (part : Fin n ≃ ι ⊕ κ) (d : Fin n →₀ ℕ) : Finset ι :=
  Finset.univ.filter fun i ↦ part.symm (Sum.inl i) ∈ d.support

/-- Support of a monomial on the right side of a partition. -/
def partitionRightSupport (part : Fin n ≃ ι ⊕ κ) (d : Fin n →₀ ℕ) : Finset κ :=
  Finset.univ.filter fun j ↦ part.symm (Sum.inr j) ∈ d.support

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem mem_partitionLeftSupport (part : Fin n ≃ ι ⊕ κ)
    (d : Fin n →₀ ℕ) (i : ι) :
    i ∈ partitionLeftSupport part d ↔ part.symm (Sum.inl i) ∈ d.support := by
  simp [partitionLeftSupport]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem mem_partitionRightSupport (part : Fin n ≃ ι ⊕ κ)
    (d : Fin n →₀ ℕ) (j : κ) :
    j ∈ partitionRightSupport part d ↔ part.symm (Sum.inr j) ∈ d.support := by
  simp [partitionRightSupport]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem partitionLeftSupport_card_le_support (part : Fin n ≃ ι ⊕ κ)
    (d : Fin n →₀ ℕ) :
    (partitionLeftSupport part d).card ≤ d.support.card := by
  apply Finset.card_le_card_of_injOn (fun i ↦ part.symm (Sum.inl i))
  · intro i hi
    exact (mem_partitionLeftSupport part d i).mp hi
  · intro i _ j _ hij
    exact Sum.inl_injective (part.symm.injective hij)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem partitionRightSupport_card_le_support (part : Fin n ≃ ι ⊕ κ)
    (d : Fin n →₀ ℕ) :
    (partitionRightSupport part d).card ≤ d.support.card := by
  apply Finset.card_le_card_of_injOn (fun j ↦ part.symm (Sum.inr j))
  · intro j hj
    exact (mem_partitionRightSupport part d j).mp hj
  · intro i _ j _ hij
    exact Sum.inr_injective (part.symm.injective hij)

omit [DecidableEq ι] [DecidableEq κ] in
/-- A monomial is one on a merged input exactly when its left and right
supports are contained in the corresponding true-coordinate sets. -/
theorem support_subset_onesSet_merge_iff (part : Fin n ≃ ι ⊕ κ)
    (d : Fin n →₀ ℕ) (u : ι → Bool) (v : κ → Bool) :
    d.support ⊆ onesSet (mergePartitionBits part u v) ↔
      partitionLeftSupport part d ⊆ trueSet u ∧
        partitionRightSupport part d ⊆ trueSet v := by
  constructor
  · intro hsub
    constructor
    · intro i hi
      have hamb := hsub ((mem_partitionLeftSupport part d i).mp hi)
      rw [mem_onesSet, mergePartitionBits_left] at hamb
      exact mem_trueSet.mpr hamb
    · intro j hj
      have hamb := hsub ((mem_partitionRightSupport part d j).mp hj)
      rw [mem_onesSet, mergePartitionBits_right] at hamb
      exact mem_trueSet.mpr hamb
  · rintro ⟨hleft, hright⟩ z hz
    cases hp : part z with
    | inl i =>
        have hzi : part.symm (Sum.inl i) = z := by
          apply part.injective
          simp [hp]
        have hi : i ∈ partitionLeftSupport part d := by
          rw [mem_partitionLeftSupport, hzi]
          exact hz
        rw [mem_onesSet]
        simpa [mergePartitionBits, hp] using mem_trueSet.mp (hleft hi)
    | inr j =>
        have hzj : part.symm (Sum.inr j) = z := by
          apply part.injective
          simp [hp]
        have hj : j ∈ partitionRightSupport part d := by
          rw [mem_partitionRightSupport, hzj]
          exact hz
        rw [mem_onesSet]
        simpa [mergePartitionBits, hp] using mem_trueSet.mp (hright hj)

/-- The subsets of a finite type whose cardinality is at most `H`. -/
noncomputable def subsetsUpToDegree (ι : Type*) [Fintype ι] (H : ℕ) :
    Finset (Finset ι) := by
  classical
  exact (Finset.range (min H (Fintype.card ι) + 1)).disjiUnion
    (fun k ↦ (Finset.univ : Finset ι).powersetCard k)
    ((Finset.univ : Finset ι).pairwise_disjoint_powersetCard.set_pairwise _)

omit [DecidableEq ι] in
theorem mem_subsetsUpToDegree_iff (S : Finset ι) (H : ℕ) :
    S ∈ subsetsUpToDegree ι H ↔ S.card ≤ H := by
  classical
  unfold subsetsUpToDegree
  rw [Finset.mem_disjiUnion]
  constructor
  · rintro ⟨k, hk, hS⟩
    have hklt : k < min H (Fintype.card ι) + 1 := Finset.mem_range.mp hk
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    omega
  · intro hcard
    refine ⟨S.card, Finset.mem_range.mpr ?_, ?_⟩
    · have hlecard : S.card ≤ Fintype.card ι := by
        simpa using Finset.card_le_card (Finset.subset_univ S)
      omega
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, rfl⟩

/-- Cardinality of the low-degree squarefree feature set. -/
theorem card_subsetsUpToDegree (ι : Type*) [Fintype ι] (H : ℕ) :
    (subsetsUpToDegree ι H).card =
      ∑ k ∈ Finset.range (min H (Fintype.card ι) + 1),
        (Fintype.card ι).choose k := by
  classical
  unfold subsetsUpToDegree
  rw [Finset.card_disjiUnion]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.card_powersetCard k Finset.univ

/-- Evaluation matrix of one monomial, already written as an outer product. -/
noncomputable def partitionMonomialMatrix (part : Fin n ≃ ι ⊕ κ)
    (P : MvPolynomial (Fin n) ℝ) (d : Fin n →₀ ℕ) :
    Matrix (ι → Bool) (κ → Bool) ℝ :=
  Matrix.vecMulVec
    (fun u ↦ if partitionLeftSupport part d ⊆ trueSet u then 1 else 0)
    (fun v ↦ P.coeff d *
      if partitionRightSupport part d ⊆ trueSet v then 1 else 0)

theorem polynomialPartitionMatrix_eq_sum_monomialMatrix
    (part : Fin n ≃ ι ⊕ κ) (P : MvPolynomial (Fin n) ℝ) :
    polynomialPartitionMatrix part P =
      ∑ d ∈ P.support, partitionMonomialMatrix part P d := by
  ext u v
  rw [polynomialPartitionMatrix, eval_cube_eq_subset_sum]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro d _
  have hiff := support_subset_onesSet_merge_iff part d u v
  simp only [partitionMonomialMatrix, Matrix.vecMulVec_apply, hiff]
  by_cases hl : partitionLeftSupport part d ⊆ trueSet u <;>
    by_cases hr : partitionRightSupport part d ⊆ trueSet v <;>
      simp [hl, hr]

/-- Group all monomials with the same left support. -/
noncomputable def leftSupportGroupMatrix (part : Fin n ≃ ι ⊕ κ)
    (P : MvPolynomial (Fin n) ℝ) (S : Finset ι) :
    Matrix (ι → Bool) (κ → Bool) ℝ :=
  ∑ d ∈ P.support with partitionLeftSupport part d = S,
    partitionMonomialMatrix part P d

theorem leftSupportGroupMatrix_rank_le_one
    (part : Fin n ≃ ι ⊕ κ) (P : MvPolynomial (Fin n) ℝ) (S : Finset ι) :
    (leftSupportGroupMatrix part P S).rank ≤ 1 := by
  let L : (ι → Bool) → ℝ := fun u ↦ if S ⊆ trueSet u then 1 else 0
  let R : (κ → Bool) → ℝ := fun v ↦
    ∑ d ∈ P.support with partitionLeftSupport part d = S,
      P.coeff d * if partitionRightSupport part d ⊆ trueSet v then 1 else 0
  have hmatrix : leftSupportGroupMatrix part P S = Matrix.vecMulVec L R := by
    ext u v
    simp only [leftSupportGroupMatrix, Matrix.sum_apply, partitionMonomialMatrix,
      Matrix.vecMulVec_apply]
    dsimp only [L, R]
    change
      (∑ d ∈ P.support with partitionLeftSupport part d = S,
          (if partitionLeftSupport part d ⊆ trueSet u then 1 else 0) *
            (P.coeff d *
              if partitionRightSupport part d ⊆ trueSet v then 1 else 0)) =
        (if S ⊆ trueSet u then 1 else 0) *
          ∑ d ∈ P.support with partitionLeftSupport part d = S,
            P.coeff d *
              if partitionRightSupport part d ⊆ trueSet v then 1 else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hsupport : partitionLeftSupport part d = S :=
      (Finset.mem_filter.mp hd).2
    rw [hsupport]
  rw [hmatrix]
  exact Matrix.rank_vecMulVec_le _ _

omit [DecidableEq ι] in
open scoped Classical in
/-- Degree-side rank cap using the left block. -/
theorem polynomialPartitionMatrix_rank_le_left
    (part : Fin n ≃ ι ⊕ κ) (P : MvPolynomial (Fin n) ℝ) (H : ℕ)
    (hP : P.totalDegree ≤ H) :
    (polynomialPartitionMatrix part P).rank ≤
      ∑ k ∈ Finset.range (min H (Fintype.card ι) + 1),
        (Fintype.card ι).choose k := by
  classical
  let low := subsetsUpToDegree ι H
  have hmaps : ∀ d ∈ P.support, partitionLeftSupport part d ∈ low := by
    intro d hd
    rw [mem_subsetsUpToDegree_iff]
    exact (partitionLeftSupport_card_le_support part d).trans
      ((support_card_le_totalDegree P hd).trans hP)
  have hgroup : polynomialPartitionMatrix part P =
      ∑ S ∈ low, leftSupportGroupMatrix part P S := by
    rw [polynomialPartitionMatrix_eq_sum_monomialMatrix]
    symm
    simpa [leftSupportGroupMatrix] using
      (Finset.sum_fiberwise_of_maps_to hmaps
        (fun d ↦ partitionMonomialMatrix part P d))
  rw [hgroup]
  refine (Matrix.rank_finset_sum_le low
    (fun S ↦ leftSupportGroupMatrix part P S)).trans ?_
  calc
    (∑ S ∈ low, (leftSupportGroupMatrix part P S).rank) ≤
        ∑ _S ∈ low, 1 :=
      Finset.sum_le_sum fun S _ ↦ leftSupportGroupMatrix_rank_le_one part P S
    _ = low.card := by simp
    _ = _ := card_subsetsUpToDegree ι H

/-- Swap the two sides of a coordinate partition. -/
def swapPartition (part : Fin n ≃ ι ⊕ κ) : Fin n ≃ κ ⊕ ι :=
  part.trans (Equiv.sumComm ι κ)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem mergePartitionBits_swap (part : Fin n ≃ ι ⊕ κ)
    (u : κ → Bool) (v : ι → Bool) :
    mergePartitionBits (swapPartition part) u v =
      mergePartitionBits part v u := by
  funext z
  cases h : part z with
  | inl i => simp [swapPartition, mergePartitionBits, h]
  | inr j => simp [swapPartition, mergePartitionBits, h]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem polynomialPartitionMatrix_swap (part : Fin n ≃ ι ⊕ κ)
    (P : MvPolynomial (Fin n) ℝ) :
    polynomialPartitionMatrix (swapPartition part) P =
      Matrix.transpose (polynomialPartitionMatrix part P) := by
  ext u v
  simp [polynomialPartitionMatrix]

omit [Fintype ι] [DecidableEq ι] in
open scoped Classical in
/-- Degree-side rank cap using the right block. -/
theorem polynomialPartitionMatrix_rank_le_right
    (part : Fin n ≃ ι ⊕ κ) (P : MvPolynomial (Fin n) ℝ) (H : ℕ)
    (hP : P.totalDegree ≤ H) :
    (polynomialPartitionMatrix part P).rank ≤
      ∑ k ∈ Finset.range (min H (Fintype.card κ) + 1),
        (Fintype.card κ).choose k := by
  letI := partitionLeftFintype part
  have hleft := polynomialPartitionMatrix_rank_le_left
    (part := swapPartition part) P H hP
  rw [polynomialPartitionMatrix_swap, Matrix.rank_transpose] at hleft
  exact hleft

end HeadComplexity
