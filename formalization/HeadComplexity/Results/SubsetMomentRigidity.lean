import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

open Finset
open scoped BigOperators

/-- The upper-subset moment transform on the Boolean lattice is injective at
zero. This is a finite algebraic statement, with no head-complexity claim. -/
theorem subset_moment_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Finset ι → ℝ)
    (hmom : ∀ T : Finset ι, (∑ S : Finset ι, if T ⊆ S then g S else 0) = 0) :
    ∀ S, g S = 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨S₀, hS₀⟩ := h
  let P : Finset (Finset ι) := univ.filter (fun S ↦ g S ≠ 0)
  have hP : P.Nonempty := ⟨S₀, by simp [P, hS₀]⟩
  obtain ⟨S, hS, hmax⟩ := P.exists_max_image Finset.card hP
  have hSne : g S ≠ 0 := (mem_filter.mp hS).2
  have hsum : (∑ R : Finset ι, if S ⊆ R then g R else 0) = g S := by
    rw [Finset.sum_eq_single S]
    · simp
    · intro R hR hRS
      by_cases hSR : S ⊆ R
      · have hgR : g R = 0 := by
          by_contra hn
          have hRP : R ∈ P := by simp [P, hn]
          have hcard : R.card ≤ S.card := hmax R hRP
          have hlt : S.card < R.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSR, Ne.symm hRS⟩)
          omega
        simp [hSR, hgR]
      · simp [hSR]
    · simp
  exact hSne (hsum.symm.trans (hmom S))

/-- Equal upper-subset moments imply equality of all Boolean-lattice masses. -/
theorem subset_moment_ext {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g h : Finset ι → ℝ)
    (hmom : ∀ T : Finset ι,
      (∑ S : Finset ι, if T ⊆ S then g S else 0) =
        ∑ S : Finset ι, if T ⊆ S then h S else 0) : g = h := by
  classical
  have hz := subset_moment_zero (fun S ↦ g S - h S) (fun T ↦ by
    calc
      (∑ S : Finset ι, if T ⊆ S then g S - h S else 0) =
          (∑ S : Finset ι, if T ⊆ S then g S else 0) -
            ∑ S : Finset ι, if T ⊆ S then h S else 0 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro S hS
        split_ifs <;> ring
      _ = 0 := sub_eq_zero.mpr (hmom T))
  funext S
  exact sub_eq_zero.mp (hz S)

/-- Any finite signed family matching every upper-subset moment of strictly
positive masses must contain a representative of every subset. The moments
1/(|T|+1) and their positive masses are established separately in the manual
permutation audit; this theorem does not assume that numerical formula. -/
theorem card_le_of_positive_subset_moments
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (R : Ω → Finset ι) (w : Ω → ℝ) (v : Finset ι → ℝ)
    (hv : ∀ S, 0 < v S)
    (hmom : ∀ T : Finset ι,
      (∑ ω, if T ⊆ R ω then w ω else 0) =
        ∑ S : Finset ι, if T ⊆ S then v S else 0) :
    2 ^ Fintype.card ι ≤ Fintype.card Ω := by
  classical
  let mass : Finset ι → ℝ := fun S ↦ ∑ ω, if R ω = S then w ω else 0
  have hmass : mass = v := by
    apply subset_moment_ext
    intro T
    calc
      (∑ S : Finset ι, if T ⊆ S then mass S else 0) =
          ∑ S : Finset ι, ∑ ω, if R ω = S then (if T ⊆ S then w ω else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro S hS
        by_cases hTS : T ⊆ S <;> simp [mass, hTS]
      _ = ∑ ω, ∑ S : Finset ι, if R ω = S then (if T ⊆ S then w ω else 0) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ ω, if T ⊆ R ω then w ω else 0 := by simp
      _ = _ := hmom T
  have hsurj : Function.Surjective R := by
    intro S
    by_contra hn
    have hnone : ∀ ω, R ω ≠ S := by simpa using hn
    have hz : mass S = 0 := by simp [mass, hnone]
    rw [hmass] at hz
    exact (ne_of_gt (hv S)) hz
  simpa using Fintype.card_le_of_surjective R hsurj

end HeadComplexity
