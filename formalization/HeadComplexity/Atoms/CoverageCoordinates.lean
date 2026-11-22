import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Coverage coordinates on the Boolean lattice

The alternating kernel below is the inverse of the nonempty-set coverage
matrix. These finite combinatorial statements do not imply any asymptotic
attention-head lower bound.
-/

namespace HeadComplexity.CoverageCoordinates

open Finset
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

lemma alternating_sum (s : Finset ι) :
    (∑ t ∈ s.powerset, (-1 : ℤ) ^ t.card) = if s = ∅ then 1 else 0 :=
  Finset.sum_powerset_neg_one_pow_card

lemma disjoint_powerset (a b : Finset ι) :
    b.powerset.filter (fun u => Disjoint a u) = (b \ a).powerset := by
  ext u
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨hub, hau⟩
    intro i hi
    exact mem_sdiff.mpr ⟨hub hi, fun hia => (Finset.disjoint_left.mp hau hia hi)⟩
  · intro hu
    constructor
    · exact fun i hi => (mem_sdiff.mp (hu hi)).1
    · exact Finset.disjoint_left.mpr fun i hia hiu => (mem_sdiff.mp (hu hiu)).2 hia

/-- A signed inclusion-exclusion sum of coverage tests is a Kronecker delta. -/
theorem coverage_kernel (a b : Finset ι) (hb : b.Nonempty) :
    (∑ u ∈ b.powerset, (-1 : ℤ) ^ (u.card + 1) *
      (if Disjoint a u then 0 else 1)) =
        if b ⊆ a then 1 else 0 := by
  have hfull : (∑ u ∈ b.powerset, (-1 : ℤ) ^ u.card) = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty hb
  have hsplit := Finset.sum_filter_add_sum_filter_not b.powerset
    (fun u => Disjoint a u) (fun u => (-1 : ℤ) ^ u.card)
  have hdis : (∑ u ∈ b.powerset.filter (fun u => Disjoint a u),
      (-1 : ℤ) ^ u.card) = if b ⊆ a then 1 else 0 := by
    rw [disjoint_powerset, alternating_sum]
    simp only [sdiff_eq_empty_iff_subset]
  have hsum : (∑ u ∈ b.powerset, (-1 : ℤ) ^ (u.card + 1) *
      (if Disjoint a u then 0 else 1)) =
      -(∑ u ∈ b.powerset.filter (fun u => ¬Disjoint a u), (-1 : ℤ) ^ u.card) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : Disjoint a u <;> simp [h, pow_succ]
  rw [hsum]
  rw [hfull, hdis] at hsplit
  omega


/-- Adding a fixed complement turns the triangular coverage kernel into a delta. -/
theorem complemented_coverage_kernel [Fintype ι] (a b : Finset ι)
    (hb : b.Nonempty) :
    (∑ u ∈ b.powerset, (-1 : ℤ) ^ (u.card + 1) *
      (if Disjoint a (bᶜ ∪ u) then 0 else 1)) = if a = b then 1 else 0 := by
  by_cases hab : a ⊆ b
  · have hd (u : Finset ι) : Disjoint a (bᶜ ∪ u) ↔ Disjoint a u := by
      rw [Finset.disjoint_union_right]
      have hc : Disjoint a bᶜ := by
        apply Finset.disjoint_left.mpr
        intro i hia hic
        exact (Finset.mem_compl.mp hic) (hab hia)
      simp [hc]
    simp_rw [hd]
    rw [coverage_kernel a b hb]
    congr 1
    exact propext ⟨fun hba => Finset.Subset.antisymm hab hba, fun h => h ▸ Finset.Subset.refl b⟩
  · have hd (u : Finset ι) : ¬Disjoint a (bᶜ ∪ u) := by
      intro h
      apply hab
      intro i hia
      by_contra hib
      exact Finset.disjoint_left.mp h hia (Finset.mem_union_left _ (Finset.mem_compl.mpr hib))
    simp_rw [ite_eq_right (hd _), mul_one, pow_succ, mul_neg, mul_one]
    rw [Finset.sum_neg_distrib, Finset.sum_powerset_neg_one_pow_card_of_nonempty hb]
    simp only [neg_zero]
    simp only [ite_eq_right (show a ≠ b from fun h => hab (h ▸ Finset.Subset.refl b))]

/-- The three exact scale identities used by the geometric-product construction. -/
theorem scale_identities (n N : ℝ) (hn : 0 < n) (hN : 0 < N) :
    N * n * (1 / (128 * n * N^3)) = (1 / (8 * N^2)) / 16 ∧
    (N^2 * (n+1) / (128*n*(n+1)*N^4)) * n = (1/(8*N^2))/16 ∧
    4*N*(1/(128*N^3)) = (1/(8*N^2))/4 := by
  have hn' : n ≠ 0 := ne_of_gt hn
  have hN' : N ≠ 0 := ne_of_gt hN
  have hnp : n+1 ≠ 0 := by positivity
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  · field_simp
    ring

#print axioms coverage_kernel
#print axioms complemented_coverage_kernel
#print axioms scale_identities

end HeadComplexity.CoverageCoordinates
