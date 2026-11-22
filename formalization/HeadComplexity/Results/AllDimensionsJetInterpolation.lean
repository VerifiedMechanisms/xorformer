import HeadComplexity.Atoms.PairCoverExtension
import HeadComplexity.Results.OpenCodeJetInterpolation
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option linter.style.header false

/-! Positive reciprocal-cube interpolation with a quadratic number of selected
columns per center, now including every Boolean input dimension at least two.
These are auxiliary jets, not actual attention-head representations. -/
namespace HeadComplexity.AllDimensionsJetInterpolation

open Finset
open scoped BigOperators symmDiff

abbrev Index (r ℓ : ℕ) := OpenCodeJetInterpolation.Index r ⊕ Fin ℓ
abbrev Centers (r ℓ : ℕ) := OpenCodeJetInterpolation.Centers r × Finset (Fin ℓ)

noncomputable def center {r ℓ : ℕ} : Centers r ℓ → Finset (Index r ℓ) :=
  PairCoverExtension.center OpenCodeJetInterpolation.center

noncomputable def owner {r ℓ : ℕ} : Finset (Index r ℓ) → Centers r ℓ :=
  PairCoverExtension.owner OpenCodeJetInterpolation.owner

noncomputable def pair {r ℓ : ℕ} : Finset (Index r ℓ) → Finset (Index r ℓ) :=
  PairCoverExtension.pair OpenCodeJetInterpolation.pair

theorem pair_card {r ℓ : ℕ} (x : Finset (Index r ℓ)) : (pair x).card = 2 := by
  classical
  exact PairCoverExtension.pair_card _ OpenCodeJetInterpolation.pair_card x

theorem target_pair {r ℓ : ℕ} (x : Finset (Index r ℓ)) :
    x ∆ center (owner x) = pair x := by
  classical
  exact PairCoverExtension.target_pair _ _ _ OpenCodeJetInterpolation.target_pair x

noncomputable def selectedNumerator {r ℓ : ℕ} (x y : Finset (Index r ℓ)) : ℝ :=
  PositivePairCover.numerator center owner pair x y

theorem exists_positive_full_rank (r ℓ : ℕ) :
    ∃ b₀ : Centers r ℓ → ℝ, ∃ b : Centers r ℓ → Index r ℓ → ℝ,
      (∀ v, 0 < b₀ v) ∧ (∀ v i, 0 < b v i) ∧
      (Matrix.of (fun x y : Finset (Index r ℓ) ↦ selectedNumerator x y /
        (b₀ (owner y) + ∑ i : Index r ℓ, b (owner y) i *
          (if i ∈ x then (1 : ℝ) else 0)) ^ 3)).det ≠ 0 := by
  classical
  exact PositivePairCover.exists_positive_affine_pair_matrix center owner pair pair_card target_pair

theorem card_index (r ℓ : ℕ) : Fintype.card (Index r ℓ) = 2 * 2 ^ r + ℓ := by
  change Fintype.card (OpenCodeJetInterpolation.Index r ⊕ Fin ℓ) = _
  rw [Fintype.card_sum, Fintype.card_fin, OpenCodeJetInterpolation.card_index]

theorem center_budget (r ℓ : ℕ) :
    Fintype.card (Centers r ℓ) * (2 ^ r) ^ 2 = Fintype.card (Finset (Index r ℓ)) := by
  classical
  have hc := OpenCodePartition.card_product_code_mul r
  change Fintype.card (OpenCodeJetInterpolation.Centers r) * (2 ^ r) ^ 2 =
    2 ^ (2 * 2 ^ r) at hc
  have hcent : Fintype.card (Centers r ℓ) =
      Fintype.card (OpenCodeJetInterpolation.Centers r) * 2 ^ ℓ := by
    rw [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
  rw [hcent, Fintype.card_finset, card_index]
  calc
    _ = (Fintype.card (OpenCodeJetInterpolation.Centers r) * (2 ^ r) ^ 2) * 2 ^ ℓ := by ring
    _ = _ := by rw [hc, ← pow_add]

theorem center_budget_lt (r ℓ : ℕ) (hℓ : ℓ < 2 * 2 ^ r) :
    Fintype.card (Centers r ℓ) * (Fintype.card (Index r ℓ)) ^ 2 <
      16 * Fintype.card (Finset (Index r ℓ)) := by
  classical
  have hb := center_budget r ℓ
  have hN : 0 < Fintype.card (Finset (Index r ℓ)) := Fintype.card_pos
  have hq : 0 < Fintype.card (Centers r ℓ) := by
    by_contra hnot
    have hz : Fintype.card (Centers r ℓ) = 0 := by omega
    rw [hz, zero_mul] at hb
    omega
  have hdim : Fintype.card (Index r ℓ) < 4 * 2 ^ r := by rw [card_index]; omega
  have hpow : (Fintype.card (Index r ℓ)) ^ 2 < (4 * 2 ^ r) ^ 2 :=
    pow_lt_pow_left₀ hdim (Nat.zero_le _) (by decide)
  calc
    _ < Fintype.card (Centers r ℓ) * (4 * 2 ^ r) ^ 2 :=
      Nat.mul_lt_mul_of_pos_left hpow hq
    _ = 16 * (Fintype.card (Centers r ℓ) * (2 ^ r) ^ 2) := by ring
    _ = _ := by rw [hb]

theorem block_parameters (n : ℕ) (hn : 2 ≤ n) :
    ∃ r ℓ : ℕ, n = 2 * 2 ^ r + ℓ ∧ ℓ < 2 * 2 ^ r := by
  let k := Nat.log 2 n
  have hk : 0 < k := Nat.log_pos (by decide) hn
  have hnzero : n ≠ 0 := by omega
  have hlow : 2 ^ k ≤ n := (Nat.le_log_iff_pow_le (by decide) hnzero).mp le_rfl
  have hupp : n < 2 ^ (k + 1) :=
    (Nat.log_lt_iff_lt_pow (by decide) hnzero).mp (Nat.lt_succ_self k)
  let r := k - 1
  have hr : r + 1 = k := by dsimp [r]; omega
  have hpower : 2 * 2 ^ r = 2 ^ k := by rw [← hr, pow_succ]; ring
  have hpower' : 4 * 2 ^ r = 2 ^ (k + 1) := by rw [pow_succ, ← hpower]; ring
  rw [← hpower] at hlow
  rw [← hpower'] at hupp
  refine ⟨r, n - 2 * 2 ^ r, ?_, ?_⟩ <;> omega

/-- Every dimension has one of the constructed matrices, with fewer than
sixteen times cube size divided by squared dimension many centers. -/
theorem every_dimension_budget (n : ℕ) (hn : 2 ≤ n) :
    ∃ r ℓ : ℕ, Fintype.card (Index r ℓ) = n ∧
      Fintype.card (Centers r ℓ) * n ^ 2 < 16 * 2 ^ n := by
  obtain ⟨r, ℓ, heq, hℓ⟩ := block_parameters n hn
  refine ⟨r, ℓ, ?_, ?_⟩
  · rw [card_index, ← heq]
  · have h := center_budget_lt r ℓ hℓ
    simpa only [Fintype.card_finset, card_index, ← heq] using h

/-- Combined existence and cardinality statement in every input dimension.
The matrix columns are quadratic reciprocal jets, not single heads. -/
theorem every_dimension_full_rank (n : ℕ) (hn : 2 ≤ n) :
    ∃ r ℓ : ℕ, Fintype.card (Index r ℓ) = n ∧
      Fintype.card (Centers r ℓ) * n ^ 2 < 16 * 2 ^ n ∧
      ∃ b₀ : Centers r ℓ → ℝ, ∃ b : Centers r ℓ → Index r ℓ → ℝ,
        (∀ v, 0 < b₀ v) ∧ (∀ v i, 0 < b v i) ∧
        (Matrix.of (fun x y : Finset (Index r ℓ) ↦ selectedNumerator x y /
          (b₀ (owner y) + ∑ i : Index r ℓ, b (owner y) i *
            (if i ∈ x then (1 : ℝ) else 0)) ^ 3)).det ≠ 0 := by
  obtain ⟨r, ℓ, hdim, hbudget⟩ := every_dimension_budget n hn
  exact ⟨r, ℓ, hdim, hbudget, exists_positive_full_rank r ℓ⟩

end HeadComplexity.AllDimensionsJetInterpolation
