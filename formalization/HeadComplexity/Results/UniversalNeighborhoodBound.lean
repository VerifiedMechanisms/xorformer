import Mathlib.Data.Nat.Log

import HeadComplexity.Results.SyndromeCoverCertificates
import HeadComplexity.Results.UniversalLinearSaving

set_option linter.style.header false

/-! # A universal head bound with constant strictly below three halves -/

namespace HeadComplexity

open Finset
open scoped BigOperators

theorem HStar_mul_pow_le_singleKernel {n k : ℕ} (hn : 2 ^ k ≤ n)
    (f : (Fin n → Bool) → Bool) : HStar n f * 2 ^ k ≤ 2 ^ n := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := ((singleKernelRecipe k).toSyndromeCover.extend extra).HStar_mul_le f
  simpa [BinaryVector, ZMod.card, SyndromeCover.extend, SyndromeRecipe.toSyndromeCover,
    singleKernelRecipe] using h

theorem HStar_mul_pow_le_syndrome12 {n s : ℕ} (hn : 12 * 2 ^ s ≤ n)
    (f : (Fin n → Bool) → Bool) : HStar n f * 2 ^ (6 + s) ≤ 7 * 2 ^ n := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := ((syndromeRecipe12.lift (by decide) s).extend extra).HStar_mul_le f
  change HStar _ f * Fintype.card (BinaryVector 6 × BinaryVector s) ≤
    (syndromeRecipe12.lift (by decide) s).targets.card * _ at h
  simpa [BinaryVector, ZMod.card, pow_add] using h

theorem HStar_mul_pow_le_syndrome13 {n s : ℕ} (hn : 13 * 2 ^ s ≤ n)
    (f : (Fin n → Bool) → Bool) : HStar n f * 2 ^ (7 + s) ≤ 12 * 2 ^ n := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := ((syndromeRecipe13.lift (by decide) s).extend extra).HStar_mul_le f
  change HStar _ f * Fintype.card (BinaryVector 7 × BinaryVector s) ≤
    (syndromeRecipe13.lift (by decide) s).targets.card * _ at h
  simpa [BinaryVector, ZMod.card, pow_add] using h

private theorem mul_budget_strict {n heads p t : ℕ}
    (hbudget : heads * p ≤ t * 2 ^ n) (hcoefficient : 2 * n * t < 3 * p) :
    2 * n * heads < 3 * 2 ^ n := by
  have hproduct : (2 * n * heads) * p < (3 * 2 ^ n) * p := by
    calc
      2 * n * heads * p = (2 * n) * (heads * p) := by ring
      _ ≤ (2 * n) * (t * 2 ^ n) := Nat.mul_le_mul_left _ hbudget
      _ = (2 * n * t) * 2 ^ n := by ring
      _ < (3 * p) * 2 ^ n := Nat.mul_lt_mul_of_pos_right hcoefficient (by positivity)
      _ = 3 * 2 ^ n * p := by ring
  exact Nat.lt_of_mul_lt_mul_right hproduct

/-- The three syndrome budgets imply the strict universal coefficient. -/
theorem two_mul_dimension_mul_cost_lt {n heads : ℕ} (hn : 8 ≤ n)
    (hkernel : ∀ k, 2 ^ k ≤ n → heads * 2 ^ k ≤ 2 ^ n)
    (htwelve : ∀ s, 12 * 2 ^ s ≤ n → heads * 2 ^ (6 + s) ≤ 7 * 2 ^ n)
    (hthirteen : ∀ s, 13 * 2 ^ s ≤ n → heads * 2 ^ (7 + s) ≤ 12 * 2 ^ n) :
    2 * n * heads < 3 * 2 ^ n := by
  let k := Nat.log 2 n
  let s := k - 3
  have hk : 3 ≤ k := Nat.le_log_of_pow_le (by decide) hn
  have hks : k = s + 3 := by dsimp [s]; omega
  have hlo : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hhi : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hp : 2 ^ k = 8 * 2 ^ s := by rw [hks, pow_add]; norm_num; ring
  have hp6 : 2 ^ (6 + s) = 64 * 2 ^ s := by rw [pow_add]; norm_num
  have hp7 : 2 ^ (7 + s) = 128 * 2 ^ s := by rw [pow_add]; norm_num
  have hupper : n < 16 * 2 ^ s := by
    have he : 2 ^ (k + 1) = 16 * 2 ^ s := by rw [hks, pow_add]; norm_num; ring
    rwa [he] at hhi
  by_cases h12 : n < 12 * 2 ^ s
  · apply mul_budget_strict (t := 1) (p := 2 ^ k)
    · simpa using hkernel k hlo
    · rw [hp]
      omega
  · by_cases h13 : n < 13 * 2 ^ s
    · apply mul_budget_strict (htwelve s (by omega))
      rw [hp6]
      omega
    · apply mul_budget_strict (hthirteen s (by omega))
      rw [hp7]
      omega

/-- Exact integer form of the three-halves universal head bound. -/
theorem two_mul_dimension_mul_HStar_lt {n : ℕ} (hn : 8 ≤ n)
    (f : (Fin n → Bool) → Bool) : 2 * n * HStar n f < 3 * 2 ^ n :=
  two_mul_dimension_mul_cost_lt hn
    (fun _ h ↦ HStar_mul_pow_le_singleKernel h f)
    (fun _ h ↦ HStar_mul_pow_le_syndrome12 h f)
    (fun _ h ↦ HStar_mul_pow_le_syndrome13 h f)

theorem HStar_real_lt_three_halves {n : ℕ} (hn : 8 ≤ n)
    (f : (Fin n → Bool) → Bool) :
    (HStar n f : ℝ) < 3 * (2 : ℝ) ^ n / (2 * n) := by
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
  have h := two_mul_dimension_mul_HStar_lt hn f
  exact_mod_cast (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)

/-- Preserve every previous endpoint and add the strict integer bound. -/
noncomputable def universalNeighborhoodBound (n : ℕ) : ℕ :=
  min (universalElevenStarBound n)
    (if 8 ≤ n then (3 * 2 ^ n - 1) / (2 * n) else universalElevenStarBound n)

theorem HStar_le_universalNeighborhoodBound {n : ℕ} (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ universalNeighborhoodBound n := by
  apply Nat.le_min.mpr
  refine ⟨HStar_le_universalElevenStarBound f, ?_⟩
  split
  · apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * n)).mpr
    have h := two_mul_dimension_mul_HStar_lt ‹8 ≤ n› f
    simpa [mul_comm] using (show 2 * n * HStar n f ≤ 3 * 2 ^ n - 1 by omega)
  · exact HStar_le_universalElevenStarBound f

theorem universalNeighborhoodBound_le_previous (n : ℕ) :
    universalNeighborhoodBound n ≤ universalElevenStarBound n := min_le_left _ _

end HeadComplexity
