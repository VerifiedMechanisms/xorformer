import HeadComplexity.Results.MultiaffinePermutation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.style.header false

/-!
# A Hall criterion from block intersections

These combinatorial lemmas audit the matching construction used in the
multiaffine counting obstruction. They assert no attention-head lower bound.
-/

namespace HeadComplexity.BlockDesignHall

open Finset
open scoped BigOperators

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- The second-order union bound, written without truncated subtraction. -/
theorem uniform_union_bound (s : Finset ι) (A : ι → Finset α) (M R : ℕ)
    (hsize : ∀ i ∈ s, (A i).card = M)
    (hinter : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (A i ∩ A j).card ≤ R) :
    2 * s.card * M + s.card * R ≤
      2 * (s.biUnion A).card + s.card ^ 2 * R := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsize' : ∀ j ∈ s, (A j).card = M :=
        fun j hj ↦ hsize j (Finset.mem_insert_of_mem hj)
      have hinter' : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → (A j ∩ A k).card ≤ R :=
        fun j hj k hk ↦ hinter j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk)
      have hind := ih hsize' hinter'
      have hAi : (A i).card = M := hsize i (Finset.mem_insert_self _ _)
      have heq : A i ∩ s.biUnion A = s.biUnion (fun j ↦ A i ∩ A j) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_biUnion]
        aesop
      have hover : (A i ∩ s.biUnion A).card ≤ s.card * R := by
        rw [heq]
        apply Finset.card_biUnion_le_card_mul
        intro j hj
        apply hinter i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        intro hij
        exact hi (hij ▸ hj)
      have hcard := Finset.card_union_add_card_inter (A i) (s.biUnion A)
      rw [hAi] at hcard
      simp only [Finset.card_insert_of_notMem hi, Finset.biUnion_insert]
      nlinarith

/-- A set of at most half the points cannot contain more than q blocks
of size q squared with pairwise intersections of size at most q. -/
theorem contained_blocks_bound (q : ℕ) (hq : 0 < q)
    (blocks : Finset (Finset α))
    (hsize : ∀ A ∈ blocks, A.card = q ^ 2)
    (hinter : ∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → (A ∩ B).card ≤ q)
    (T : Finset α) (hT : 2 * T.card ≤ q ^ 3) :
    (blocks.filter fun A ↦ A ⊆ T).card ≤ q := by
  classical
  by_contra! hbad
  obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hbad)
  have hsblocks : s ⊆ blocks := fun A hA ↦ (Finset.mem_filter.mp (hs hA)).1
  have hsT : s.biUnion id ⊆ T := by
    intro x hx
    obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp (hs hA)).2 hxA
  have hu := uniform_union_bound s id (q ^ 2) q
    (fun A hA ↦ hsize A (hsblocks hA))
    (fun A hA B hB ↦ hinter A (hsblocks hA) B (hsblocks hB))
  rw [hscard] at hu
  have hucard := Finset.card_le_card hsT
  nlinarith [sq_pos_of_pos (show (0 : ℤ) < q by exact_mod_cast hq)]

variable {κ β : Type*} [Fintype α] [Fintype κ] [Fintype β]
    [DecidableEq κ] [DecidableEq β]

/-- The block-size, intersection, and multiplicity estimates imply the
small-set Hall condition for every simultaneous choice of colors. -/
theorem color_hall_of_blocks (q r : ℕ) (hq : 0 < q)
    (blocks : Finset (Finset α)) (c : κ → α → β)
    (hsize : ∀ A ∈ blocks, A.card = q ^ 2)
    (hinter : ∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → (A ∩ B).card ≤ q)
    (hfiber : ∀ k b, (Finset.univ.filter fun x ↦ c k x = b) ∈ blocks)
    (hmult : ∀ A ∈ blocks,
      (Finset.univ.filter fun k ↦
        ∃ b, (Finset.univ.filter fun x ↦ c k x = b) = A).card ≤ r)
    (hnumber : 2 * Fintype.card κ ≤ q ^ 3) (hrep : q * r ≤ q ^ 2)
    (T : Finset α) (hT : T.card < Fintype.card κ) :
    (Finset.univ.filter fun k ↦
      ∃ b, (Finset.univ.filter fun x ↦ c k x = b) ⊆ T).card ≤ T.card := by
  classical
  by_cases hsmall : T.card < q ^ 2
  · have hempty : (Finset.univ.filter fun k ↦
        ∃ b, (Finset.univ.filter fun x ↦ c k x = b) ⊆ T) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hk).2
      have hcard := Finset.card_le_card hb
      rw [hsize _ (hfiber k b)] at hcard
      exact (not_lt_of_ge hcard) hsmall
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · let contained := blocks.filter fun A ↦ A ⊆ T
    let occurrences : Finset α → Finset κ := fun A ↦
      Finset.univ.filter fun k ↦
        ∃ b, (Finset.univ.filter fun x ↦ c k x = b) = A
    have hcontained : contained.card ≤ q :=
      contained_blocks_bound q hq blocks hsize hinter T (by omega)
    have hsubset : (Finset.univ.filter fun k ↦
        ∃ b, (Finset.univ.filter fun x ↦ c k x = b) ⊆ T) ⊆
        contained.biUnion occurrences := by
      intro k hk
      obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hk).2
      apply Finset.mem_biUnion.mpr
      refine ⟨Finset.univ.filter (fun x ↦ c k x = b), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hfiber k b, hb⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, b, rfl⟩
    calc
      _ ≤ (contained.biUnion occurrences).card := Finset.card_le_card hsubset
      _ ≤ contained.card * r := Finset.card_biUnion_le_card_mul _ _ _
        (fun A hA ↦ hmult A (Finset.mem_filter.mp hA).1)
      _ ≤ q * r := Nat.mul_le_mul_right r hcontained
      _ ≤ q ^ 2 := hrep
      _ ≤ T.card := Nat.le_of_not_gt hsmall

theorem exists_representatives_of_blocks (q r : ℕ) (hq : 0 < q)
    (blocks : Finset (Finset α)) (c : κ → α → β)
    (hsize : ∀ A ∈ blocks, A.card = q ^ 2)
    (hinter : ∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → (A ∩ B).card ≤ q)
    (hfiber : ∀ k b, (Finset.univ.filter fun x ↦ c k x = b) ∈ blocks)
    (hmult : ∀ A ∈ blocks,
      (Finset.univ.filter fun k ↦
        ∃ b, (Finset.univ.filter fun x ↦ c k x = b) = A).card ≤ r)
    (hnumber : 2 * Fintype.card κ ≤ q ^ 3) (hrep : q * r ≤ q ^ 2)
    (target : κ → β) :
    ∃ f : κ → α, Function.Injective f ∧ ∀ k, c k (f k) = target k := by
  apply MultiaffinePermutation.exists_color_representatives c
    (color_hall_of_blocks q r hq blocks c hsize hinter hfiber hmult hnumber hrep) target

/- The sharper estimate for lines, allowing q/2 repetitions of each
parallel class in an affine plane. -/
omit [Fintype α] in
theorem contained_lines_weight_bound (q r : ℕ)
    (blocks : Finset (Finset α))
    (hsize : ∀ A ∈ blocks, A.card = q)
    (hinter : ∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → (A ∩ B).card ≤ 1)
    (T : Finset α) (hT : 2 * T.card < q * (q + 1)) (hr : 2 * r ≤ q) :
    (blocks.filter fun A ↦ A ⊆ T).card * r ≤ T.card := by
  classical
  let contained := blocks.filter fun A ↦ A ⊆ T
  have hsub : contained.biUnion id ⊆ T := by
    intro x hx
    obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hA).2 hxA
  have hsmall : contained.card ≤ q := by
    by_contra! hbad
    obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hbad)
    have hsblocks : s ⊆ blocks := fun A hA ↦ (Finset.mem_filter.mp (hs hA)).1
    have hsT : s.biUnion id ⊆ T := by
      intro x hx
      obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp (hs hA)).2 hxA
    have hu := uniform_union_bound s id q 1
      (fun A hA ↦ hsize A (hsblocks hA))
      (fun A hA B hB ↦ hinter A (hsblocks hA) B (hsblocks hB))
    rw [hscard] at hu
    have hucard := Finset.card_le_card hsT
    nlinarith
  have hu := uniform_union_bound contained id q 1
    (fun A hA ↦ hsize A (Finset.mem_filter.mp hA).1)
    (fun A hA B hB ↦ hinter A (Finset.mem_filter.mp hA).1
      B (Finset.mem_filter.mp hB).1)
  have hucard := Finset.card_le_card hsub
  have hprod := Nat.mul_le_mul_left contained.card hsmall
  have hrprod := Nat.mul_le_mul_left contained.card hr
  change contained.card * r ≤ T.card
  nlinarith

theorem color_hall_of_contained_bound (r : ℕ)
    (blocks : Finset (Finset α)) (c : κ → α → β)
    (hfiber : ∀ k b, (Finset.univ.filter fun x ↦ c k x = b) ∈ blocks)
    (hmult : ∀ A ∈ blocks,
      (Finset.univ.filter fun k ↦
        ∃ b, (Finset.univ.filter fun x ↦ c k x = b) = A).card ≤ r)
    (hcapacity : ∀ T : Finset α, T.card < Fintype.card κ →
      (blocks.filter fun A ↦ A ⊆ T).card * r ≤ T.card)
    (T : Finset α) (hT : T.card < Fintype.card κ) :
    (Finset.univ.filter fun k ↦
      ∃ b, (Finset.univ.filter fun x ↦ c k x = b) ⊆ T).card ≤ T.card := by
  classical
  let contained := blocks.filter fun A ↦ A ⊆ T
  let occurrences : Finset α → Finset κ := fun A ↦
    Finset.univ.filter fun k ↦
      ∃ b, (Finset.univ.filter fun x ↦ c k x = b) = A
  have hsubset : (Finset.univ.filter fun k ↦
      ∃ b, (Finset.univ.filter fun x ↦ c k x = b) ⊆ T) ⊆
      contained.biUnion occurrences := by
    intro k hk
    obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hk).2
    apply Finset.mem_biUnion.mpr
    refine ⟨Finset.univ.filter (fun x ↦ c k x = b), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hfiber k b, hb⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, b, rfl⟩
  calc
    _ ≤ (contained.biUnion occurrences).card := Finset.card_le_card hsubset
    _ ≤ contained.card * r := Finset.card_biUnion_le_card_mul _ _ _
      (fun A hA ↦ hmult A (Finset.mem_filter.mp hA).1)
    _ ≤ T.card := hcapacity T hT

end HeadComplexity.BlockDesignHall
