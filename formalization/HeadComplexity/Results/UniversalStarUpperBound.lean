import HeadComplexity.Results.CountingLowerBound
import HeadComplexity.Results.StarDegreeUpperBound
import HeadComplexity.Results.WeightedUpperBound

set_option linter.style.header false

/-!
# Universal improvement of the original interpolation bound

The parity-rank star cover has exactly half of the subsets in every positive
dimension. Thus every truth table has an actual attention realization with
`2^(n-1)` heads, improving the original `2^n - 1` universal bound.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

/-- Exactly half of all coordinate sets have either specified parity. -/
theorem card_parity_coordinateSets {n : ℕ} (hn : 0 < n) (b : ℕ) (hb : b < 2) :
    ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S ↦ S.card % 2 = b)).card = 2 ^ (n - 1) := by
  classical
  let i : Fin n := ⟨0, hn⟩
  have hcard :
      ((Finset.univ : Finset (Finset (Fin n))).filter
        (fun S ↦ S.card % 2 = b)).card =
      ((Finset.univ.erase i : Finset (Fin n)).powerset).card := by
    apply Finset.card_bij (fun S _ ↦ S.erase i)
    · intro S _
      simp only [Finset.mem_powerset]
      intro j hj
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ j⟩
    · intro S hS T hT heq
      have hSpar := (Finset.mem_filter.mp hS).2
      have hTpar := (Finset.mem_filter.mp hT).2
      have hc := congrArg Finset.card heq
      by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
      · calc
          S = insert i (S.erase i) := (Finset.insert_erase hiS).symm
          _ = insert i (T.erase i) := congrArg (insert i) heq
          _ = T := Finset.insert_erase hiT
      · rw [Finset.card_erase_of_mem hiS, Finset.erase_eq_of_notMem hiT] at hc
        have := Finset.card_pos.mpr ⟨i, hiS⟩
        omega
      · rw [Finset.erase_eq_of_notMem hiS, Finset.card_erase_of_mem hiT] at hc
        have := Finset.card_pos.mpr ⟨i, hiT⟩
        omega
      · simpa [Finset.erase_eq_of_notMem hiS, Finset.erase_eq_of_notMem hiT] using heq
    · intro T hT
      have hiT : i ∉ T := by
        have hsub := Finset.mem_powerset.mp hT
        exact fun hi ↦ Finset.notMem_erase i Finset.univ (hsub hi)
      by_cases hpar : T.card % 2 = b
      · exact ⟨T, by simp [hpar], Finset.erase_eq_of_notMem hiT⟩
      · refine ⟨insert i T, ?_, by simp [hiT]⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.card_insert_of_notMem hiT]
        omega
  rw [hcard, Finset.card_powerset]
  simp

/-- At ambient degree, all sets of parity `n - 1` are selected, including
exactly half of all coordinate sets. -/
theorem starDegreeBound_ambient {n : ℕ} (hn : 0 < n) :
    starDegreeBound n n = 2 ^ (n - 1) := by
  rw [← card_degreeStarCenters]
  have hcenters : degreeStarCenters n n =
      (Finset.univ : Finset (Finset (Fin n))).filter
        (fun S ↦ S.card % 2 = (n - 1) % 2) := by
    ext S
    simp only [degreeStarCenters, Finset.mem_filter, Finset.mem_univ,
      true_and, starCenterRanks, Finset.mem_range]
    have hcard : S.card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    omega
  rw [hcenters]
  exact card_parity_coordinateSets hn _ (Nat.mod_lt _ (by decide))

/-- Every Boolean truth table in positive dimension has an actual
`2^(n-1)`-head attention realization. -/
theorem computableWithHeadsN_two_pow_pred {n : ℕ} (hn : 0 < n)
    (f : (Fin n → Bool) → Bool) :
    computableWithHeadsN n (2 ^ (n - 1)) f := by
  obtain ⟨P, _, hP⟩ :=
    SquarefreePolynomial.exists_squarefree_strictSignRep_of_ThresholdDegLE
      (thresholdDeg_spec f)
  have hdeg : P.DegreeLE n := by
    intro S _
    simpa using Finset.card_le_card (Finset.subset_univ S)
  have hcomp := P.computableWithHeadsN_of_starCover f hP
    (degreeStarCenters n n) (P.hasStarCover_degreeStarCenters hdeg)
  rwa [card_degreeStarCenters, starDegreeBound_ambient hn] at hcomp

/-- The original universal head upper bound improves from `2^n - 1` to
`2^(n-1)` in every positive dimension. -/
theorem HStar_le_two_pow_pred {n : ℕ} (hn : 0 < n)
    (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ 2 ^ (n - 1) :=
  HStar_le_of_computableWithHeadsN (computableWithHeadsN_two_pow_pred hn f)

/-- An unconditional joint form, retaining the zero-dimensional endpoint. -/
theorem HStar_le_min_universal_star {n : ℕ} (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ min (2 ^ n - 1) (2 ^ (n - 1)) := by
  apply Nat.le_min.mpr
  refine ⟨HStar_le_universal_boolean f, ?_⟩
  by_cases hn : 0 < n
  · exact HStar_le_two_pow_pred hn f
  · have hn0 : n = 0 := by omega
    have hold := HStar_le_universal_boolean f
    simpa [hn0] using hold.trans (by simp [hn0] : 2 ^ n - 1 ≤ 2 ^ (n - 1))

/-- The improved universal budget is strictly smaller in every dimension
at least two. This compares numerical bounds applicable to every function. -/
theorem two_pow_pred_lt_original_universal {n : ℕ} (hn : 2 ≤ n) :
    2 ^ (n - 1) < 2 ^ n - 1 := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    omega
  have hlarge : 2 ≤ 2 ^ (n - 1) := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ n - 1)
    simpa using this
  omega

/-- Worst-case presentation of the universal strengthening. -/
theorem worstCaseHeadComplexity_le_two_pow_pred {n : ℕ} (hn : 0 < n) :
    worstCaseHeadComplexity n ≤ 2 ^ (n - 1) := by
  apply Finset.sup_le
  intro f _
  exact HStar_le_two_pow_pred hn f

end HeadComplexity
