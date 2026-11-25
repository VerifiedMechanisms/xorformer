import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option linter.style.header false

/-! Quantitative finite rank gluing. This numerical lemma does not assert
that unrestricted xorformer tables admit the required local modules. -/

namespace HeadComplexity.QuantitativeRankGluing

open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- A large penalty bounds every scaled outside contribution. -/
theorem scaled_tail_le {n k : ℕ} {C B T : ℝ}
    (hC : 1 ≤ C) (hB : 0 ≤ B) (hT : 0 < T)
    (hbudget : 8 * (Fintype.card I : ℝ) * C ^ n * B ≤ T)
    (hcard : 0 < Fintype.card I) {v : ℝ} (hv : |v| ≤ B / T) :
    C ^ (n - k) * |v| ≤ 1 / (8 * (Fintype.card I : ℝ)) := by
  have hM : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hcard
  have hpow : 0 ≤ C ^ (n - k) := pow_nonneg (by linarith) _
  have hpowle : C ^ (n - k) ≤ C ^ n :=
    pow_le_pow_right₀ hC (Nat.sub_le _ _)
  have hnum : C ^ (n - k) * B * (8 * (Fintype.card I : ℝ)) ≤ T := by
    have hmult := mul_le_mul_of_nonneg_right hpowle hB
    have hmult' := mul_le_mul_of_nonneg_left hmult
      (by positivity : 0 ≤ 8 * (Fintype.card I : ℝ))
    nlinarith
  apply (mul_le_mul_of_nonneg_left hv hpow).trans
  apply (le_div_iff₀ (by positivity : 0 < 8 * (Fintype.card I : ℝ))).mpr
  have hh : (C ^ (n - k) * B * (8 * (Fintype.card I : ℝ))) / T ≤ 1 :=
    (div_le_iff₀ hT).mpr (by simpa using hnum)
  convert hh using 1
  ring

/-- One scale per rank suffices. The values already include the desired label
sign. Inside the localized regions, lower ranks are nonnegative; outside,
the tails have an explicit bound. -/
theorem rank_weighted_sum_gap {n r : ℕ} (rank : I → ℕ) (inside : I → Prop)
    (v : I → ℝ) (B C : ℝ)
    (hcard : 0 < Fintype.card I) (hB : 1 ≤ B)
    (hC : 8 * (Fintype.card I : ℝ) * B ≤ C)
    (hr : r ≤ n) (hrank : ∀ i, rank i ≤ n)
    (hbound : ∀ i, |v i| ≤ B)
    (hcompat : ∀ i, inside i → rank i ≤ r → 0 ≤ v i)
    (htail : ∀ i, ¬inside i →
      C ^ (n - rank i) * |v i| ≤ 1 / (8 * (Fintype.card I : ℝ)))
    (j : I) (hjrank : rank j = r) (hj : 1 ≤ v j) :
    (1 / 2 : ℝ) ≤ ∑ i, C ^ (n - rank i) * v i := by
  classical
  have hM : 0 < (Fintype.card I : ℝ) := by exact_mod_cast hcard
  have hMone : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast hcard
  have hC1 : 1 ≤ C := by nlinarith
  have hCpos : 0 < C := by linarith
  let a : ℝ := C ^ (n - r)
  let e : ℝ := (a + 1) / (8 * (Fintype.card I : ℝ))
  have ha : 1 ≤ a := one_le_pow₀ hC1
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hterm : ∀ i, 0 ≤ C ^ (n - rank i) * v i + e := by
    intro i
    have hpow : 0 ≤ C ^ (n - rank i) := pow_nonneg hCpos.le _
    have hneg : -(C ^ (n - rank i) * |v i|) ≤
        C ^ (n - rank i) * v i := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le (v i)) hpow
      nlinarith
    by_cases hi : inside i
    · by_cases hri : rank i ≤ r
      · exact add_nonneg (mul_nonneg hpow (hcompat i hi hri)) he
      · have hexp : n - rank i + 1 ≤ n - r := by have := hrank i; omega
        have hpower : C ^ (n - rank i) * C ≤ a := by
          dsimp [a]
          rw [← pow_succ]
          exact pow_le_pow_right₀ hC1 hexp
        have hb : C ^ (n - rank i) * B ≤ a / (8 * (Fintype.card I : ℝ)) := by
          apply (le_div_iff₀ (by positivity : 0 < 8 * (Fintype.card I : ℝ))).mpr
          have hm := mul_le_mul_of_nonneg_left hC hpow
          nlinarith
        have hv := mul_le_mul_of_nonneg_left (hbound i) hpow
        have hae : a / (8 * (Fintype.card I : ℝ)) ≤ e := by
          dsimp [e]
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
        linarith
    · have ht := htail i hi
      have h1e : 1 / (8 * (Fintype.card I : ℝ)) ≤ e := by
        dsimp [e]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith
  have hsingle := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hterm i)
    (Finset.mem_univ j)
  have hmain : a ≤ C ^ (n - rank j) * v j := by
    rw [hjrank]
    have hp : 0 ≤ C ^ (n - r) := pow_nonneg hCpos.le _
    simpa [a] using mul_le_mul_of_nonneg_left hj hp
  have hsum : (∑ i, (C ^ (n - rank i) * v i + e)) =
      (∑ i, C ^ (n - rank i) * v i) + (Fintype.card I : ℝ) * e := by
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum] at hsingle
  have hMe : (Fintype.card I : ℝ) * e = (a + 1) / 8 := by
    dsimp [e]
    field_simp
  rw [hMe] at hsingle
  linarith

/-- Total module mass grows by at most the largest rank weight. -/
theorem rank_weighted_mass_le {n : ℕ} (rank : I → ℕ) (mass : I → ℝ)
    {B C : ℝ} (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hmass : ∀ i, mass i ≤ B) :
    (∑ i, C ^ (n - rank i) * mass i) ≤
      (Fintype.card I : ℝ) * C ^ n * B := by
  calc
    (∑ i, C ^ (n - rank i) * mass i) ≤ ∑ _ : I, C ^ n * B := by
      apply Finset.sum_le_sum
      intro i _
      apply (mul_le_mul_of_nonneg_left (hmass i)
        (pow_nonneg (by linarith : 0 ≤ C) _)).trans
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hC (Nat.sub_le _ _)) hB
    _ = _ := by simp [mul_assoc]

end HeadComplexity.QuantitativeRankGluing
