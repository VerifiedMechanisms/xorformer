import HeadComplexity.Results.FixedDenominatorSignBarrier
import Mathlib.Combinatorics.SetFamily.Shatter

set_option linter.style.header false

/-!
# Capacity of a finite library of fixed denominator lists

The numerator coefficients remain arbitrary real numbers. A fixed linear
score space has VC dimension at most its parameter dimension, so the
Sauer bound controls each list. No claim of universality for a small
denominator library is made.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

/-- Subsets that occur as the positive coordinates of a strict score from
the specified linear parameterization. -/
noncomputable def linearStrictSignSets
    {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] (I → ℝ)) : Finset (Finset I) := by
  classical
  exact Finset.univ.filter fun s ↦ ∃ v : V,
    ∀ i, if i ∈ s then 0 < L v i else L v i < 0

theorem card_le_finrank_of_linearStrictSignSets_shatters
    {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (L : V →ₗ[ℝ] (I → ℝ))
    (s : Finset I) (hs : (linearStrictSignSets L).Shatters s) :
    s.card ≤ Module.finrank ℝ V := by
  classical
  let Ls : V →ₗ[ℝ] (s → ℝ) :=
    { toFun := fun v i ↦ L v i
      map_add' := by intro a b; ext i; simp
      map_smul' := by intro a b; ext i; simp }
  have hLs : MeetsEveryStrictOrthant Ls.range := by
    intro signs
    let t := s.filter fun i ↦ ∃ hi : i ∈ s, signs ⟨i, hi⟩ = true
    obtain ⟨u, hu, hsu⟩ := hs (Finset.filter_subset _ _ : t ⊆ s)
    obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hu).2
    refine ⟨Ls v, ⟨v, rfl⟩, fun i ↦ ?_⟩
    have htrace : (i.val ∈ u) ↔ signs i = true := by
      have ht := congrArg (fun a : Finset I ↦ i.val ∈ a) hsu
      simpa [t, i.property] using ht
    have hi := hv i.val
    cases hsi : signs i with
    | false =>
        have hnot : i.val ∉ u := by simpa [hsi] using htrace
        simpa [Ls, hnot] using hi
    | true =>
        have hmem : i.val ∈ u := htrace.mpr hsi
        simpa [Ls, hmem] using hi
  simpa using card_le_finrank_of_range_meetsEveryStrictOrthant Ls hLs

theorem linearStrictSignSets_vcDim_le
    {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (L : V →ₗ[ℝ] (I → ℝ)) :
    (linearStrictSignSets L).vcDim ≤ Module.finrank ℝ V := by
  classical
  apply Finset.sup_le
  intro s hs
  exact card_le_finrank_of_linearStrictSignSets_shatters L s
    (Finset.mem_shatterer.mp hs)

/-- An unconditional Sauer bound for the strict sign patterns of a linear
score family. -/
theorem card_linearStrictSignSets_le_sum_choose
    {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (L : V →ₗ[ℝ] (I → ℝ)) :
    (linearStrictSignSets L).card ≤
      ∑ j ∈ Finset.Iic (Module.finrank ℝ V), (Fintype.card I).choose j := by
  classical
  calc
    (linearStrictSignSets L).card ≤ (linearStrictSignSets L).shatterer.card :=
      Finset.card_le_card_shatterer _
    _ ≤ ∑ j ∈ Finset.Iic (linearStrictSignSets L).vcDim,
        (Fintype.card I).choose j := Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ j ∈ Finset.Iic (Module.finrank ℝ V), (Fintype.card I).choose j := by
      exact Finset.sum_le_sum_of_subset
        (Finset.Iic_subset_Iic.mpr (linearStrictSignSets_vcDim_le L))

/-- A finite union of linear score families can be universal only if the
sum of their Sauer capacities covers all Boolean truth tables. -/
theorem two_pow_card_le_library_card_mul_sum_choose
    {I V K : Type*} [Fintype I] [Fintype K]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : K → V →ₗ[ℝ] (I → ℝ))
    (huniversal : ∀ f : I → Bool, ∃ k : K, ∃ v : V,
      ∀ i, if f i then 0 < L k v i else L k v i < 0) :
    2 ^ Fintype.card I ≤ Fintype.card K *
      ∑ j ∈ Finset.Iic (Module.finrank ℝ V), (Fintype.card I).choose j := by
  classical
  have hcover : (Finset.univ : Finset (Finset I)) ⊆
      Finset.univ.biUnion (fun k ↦ linearStrictSignSets (L k)) := by
    intro s _
    obtain ⟨k, v, hv⟩ := huniversal (fun i ↦ decide (i ∈ s))
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, v, by simpa using hv⟩
  calc
    2 ^ Fintype.card I = (Finset.univ : Finset (Finset I)).card := by simp
    _ ≤ (Finset.univ.biUnion (fun k ↦ linearStrictSignSets (L k))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ k : K, (linearStrictSignSets (L k)).card := Finset.card_biUnion_le
    _ ≤ ∑ _k : K, ∑ j ∈ Finset.Iic (Module.finrank ℝ V),
        (Fintype.card I).choose j := by
      exact Finset.sum_le_sum fun k _ ↦ card_linearStrictSignSets_le_sum_choose (L k)
    _ = Fintype.card K *
        ∑ j ∈ Finset.Iic (Module.finrank ℝ V), (Fintype.card I).choose j := by
      simp

/-- Fixed denominator lists, with arbitrary real numerator coefficients,
obey the finite library capacity inequality. This also bounds every
admissible affine denominator library, since no denominator condition is
needed for this upper count. -/
theorem two_pow_two_pow_le_denominator_library_capacity
    {n H : ℕ} {K : Type*} [Fintype K]
    (B : K → Fin H → (Fin n → Bool) → ℝ)
    (huniversal : ∀ f : (Fin n → Bool) → Bool, ∃ k : K,
      ∃ θ : FixedFractionParameter n H → ℝ, ∀ x,
        if f x then
          0 < Fintype.linearCombination ℝ (fixedFractionFeature (B k)) θ x
        else Fintype.linearCombination ℝ (fixedFractionFeature (B k)) θ x < 0) :
    2 ^ (2 ^ n) ≤ Fintype.card K *
      ∑ j ∈ Finset.Iic (1 + H * n), (2 ^ n).choose j := by
  simpa [FixedFractionParameter, Fintype.card_bool] using
    two_pow_card_le_library_card_mul_sum_choose
      (fun k ↦ Fintype.linearCombination ℝ (fixedFractionFeature (B k))) huniversal

/-- A normalized affine denominator whose nonconstant coefficients come
from the designated finite alphabet. Positivity is not asserted by this
definition: imposing admissibility only reduces the family being counted. -/
noncomputable def alphabetAffineDenominator {n H : ℕ}
    (alphabet : Finset ℝ) (β : (Fin H × Fin n) → alphabet)
    (h : Fin H) (x : Fin n → Bool) : ℝ :=
  1 + ∑ i, (β (h, i) : ℝ) * (if x i then 1 else 0)

/-- The exact denominator-only information inequality, in exponentiated
form. All numerator coefficients and the bias remain arbitrary reals. -/
theorem two_pow_two_pow_le_bits_denominator_capacity
    {n H b : ℕ} (alphabet : Finset ℝ)
    (halphabet : alphabet.card ≤ 2 ^ b)
    (huniversal : ∀ f : (Fin n → Bool) → Bool,
      ∃ β : (Fin H × Fin n) → alphabet,
      ∃ θ : FixedFractionParameter n H → ℝ, ∀ x,
        if f x then
          0 < Fintype.linearCombination ℝ
            (fixedFractionFeature (alphabetAffineDenominator alphabet β)) θ x
        else Fintype.linearCombination ℝ
            (fixedFractionFeature (alphabetAffineDenominator alphabet β)) θ x < 0) :
    2 ^ (2 ^ n) ≤ 2 ^ (b * (H * n)) *
      ∑ j ∈ Finset.Iic (1 + H * n), (2 ^ n).choose j := by
  have h := two_pow_two_pow_le_denominator_library_capacity
    (alphabetAffineDenominator alphabet) huniversal
  have hc : Fintype.card ((Fin H × Fin n) → alphabet) ≤ 2 ^ (b * (H * n)) := by
    calc
      Fintype.card ((Fin H × Fin n) → alphabet) = alphabet.card ^ (H * n) := by simp
      _ ≤ (2 ^ b) ^ (H * n) := Nat.pow_le_pow_left halphabet _
      _ = 2 ^ (b * (H * n)) := (pow_mul _ _ _).symm
  exact h.trans (Nat.mul_le_mul_right _ hc)

end HeadComplexity
