import HeadComplexity.Research.MarginCapacityEstimates

set_option linter.style.header false

/-!
Exact implications from either a truth-table-preserving margin repair or a
bound on the universally low-margin class to the original worst-case head
complexity. None of the repair or low-margin hypotheses is proved here.
-/

noncomputable section

namespace HeadComplexity.ConditionalMarginLowerBounds

open RelativeMarginQuantifiers MarginCapacityEstimates

variable {n H K B : ℕ} {C gamma : ℝ}

theorem two_half_counts_lt (hn : 2 ≤ n) :
    2 ^ (2 ^ (n - 1)) + 2 ^ (2 ^ (n - 1)) < 2 ^ (2 ^ n) := by
  have hhalf : 1 < 2 ^ (n - 1) := by
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hexp : 2 ^ (n - 1) + 1 < 2 ^ n := by omega
  calc
    _ = 2 ^ (2 ^ (n - 1) + 1) := by rw [pow_succ]; omega
    _ < _ := pow_lt_pow_right₀ (by norm_num) hexp

/-- The exceptional class here has the universal quantifier over all
comparison-width representations, exactly as defined in the margin API. -/
theorem worstCase_gt_of_two_half_counts (hn : 2 ≤ n)
    (hhigh : (highMarginFunctions n K gamma).ncard ≤ 2 ^ (2 ^ (n - 1)))
    (hlow : (allRepresentationsLowMargin n H K gamma).ncard ≤ 2 ^ (2 ^ (n - 1))) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_high_and_low_counts hhigh hlow (two_half_counts_lt hn)

theorem lowMargin_eq_empty_of_repair
    (hrepair : ∀ f, computableWithHeadsN n H f → HasRelativeMargin n K f gamma) :
    allRepresentationsLowMargin n H K gamma = ∅ := by
  ext f
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hf
  exact hf.2 (hrepair f hf.1)

theorem worstCase_gt_of_repair_and_half_count (hn : 2 ≤ n)
    (hhigh : (highMarginFunctions n K gamma).ncard ≤ 2 ^ (2 ^ (n - 1)))
    (hrepair : ∀ f, computableWithHeadsN n H f → HasRelativeMargin n K f gamma) :
    H < worstCaseHeadComplexity n := by
  apply worstCase_gt_of_two_half_counts hn hhigh
  rw [lowMargin_eq_empty_of_repair hrepair, Set.ncard_empty]
  exact Nat.zero_le _

theorem worstCase_gt_sqrt_of_low_count
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * C * n * Real.sqrt n))
    (hlow : (allRepresentationsLowMargin n H (⌈C * (H : ℝ)⌉₊ + B)
      (Real.exp (-Real.exp (Real.sqrt n)))).ncard ≤ 2 ^ (2 ^ (n - 1))) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_two_half_counts (by omega)
    (card_highMargin_sqrt_overhead hn hC hoverhead hwidth) hlow

theorem worstCase_gt_sqrt_of_repair
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * C * n * Real.sqrt n))
    (hrepair : ∀ f, computableWithHeadsN n H f →
      HasRelativeMargin n (⌈C * (H : ℝ)⌉₊ + B) f
        (Real.exp (-Real.exp (Real.sqrt n)))) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_repair_and_half_count (by omega)
    (card_highMargin_sqrt_overhead hn hC hoverhead hwidth) hrepair

theorem worstCase_gt_logarithmic_of_low_count
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2))
    (hlow : (allRepresentationsLowMargin n H (⌈C * (H : ℝ)⌉₊ + B)
      (Real.exp (-Real.exp ((n : ℝ) / Real.log n)))).ncard ≤ 2 ^ (2 ^ (n - 1))) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_two_half_counts (by omega)
    (card_highMargin_logarithmic_overhead hn hC hoverhead hwidth) hlow

theorem worstCase_gt_logarithmic_of_repair
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2))
    (hrepair : ∀ f, computableWithHeadsN n H f →
      HasRelativeMargin n (⌈C * (H : ℝ)⌉₊ + B) f
        (Real.exp (-Real.exp ((n : ℝ) / Real.log n)))) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_repair_and_half_count (by omega)
    (card_highMargin_logarithmic_overhead hn hC hoverhead hwidth) hrepair

/-- The natural floor incurs no loss in the final real lower bound. -/
theorem real_sqrt_bound_of_low_count
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hlow : (allRepresentationsLowMargin n
      ⌊(2 : ℝ) ^ n / (100 * C * n * Real.sqrt n)⌋₊
      (⌈C * (⌊(2 : ℝ) ^ n / (100 * C * n * Real.sqrt n)⌋₊ : ℝ)⌉₊ + B)
      (Real.exp (-Real.exp (Real.sqrt n)))).ncard ≤ 2 ^ (2 ^ (n - 1))) :
    (2 : ℝ) ^ n / (100 * C * n * Real.sqrt n) < worstCaseHeadComplexity n := by
  apply Nat.lt_of_floor_lt
  apply worstCase_gt_sqrt_of_low_count hn hC hoverhead _ hlow
  apply Nat.floor_le
  positivity

theorem real_logarithmic_bound_of_low_count
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hlow : (allRepresentationsLowMargin n
      ⌊(2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2)⌋₊
      (⌈C * (⌊(2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2)⌋₊ : ℝ)⌉₊ + B)
      (Real.exp (-Real.exp ((n : ℝ) / Real.log n)))).ncard ≤ 2 ^ (2 ^ (n - 1))) :
    (2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2) < worstCaseHeadComplexity n := by
  apply Nat.lt_of_floor_lt
  apply worstCase_gt_logarithmic_of_low_count hn hC hoverhead _ hlow
  apply Nat.floor_le
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  positivity

theorem real_sqrt_bound_of_repair
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hrepair : ∀ f,
      computableWithHeadsN n ⌊(2 : ℝ) ^ n / (100 * C * n * Real.sqrt n)⌋₊ f →
      HasRelativeMargin n
        (⌈C * (⌊(2 : ℝ) ^ n / (100 * C * n * Real.sqrt n)⌋₊ : ℝ)⌉₊ + B) f
        (Real.exp (-Real.exp (Real.sqrt n)))) :
    (2 : ℝ) ^ n / (100 * C * n * Real.sqrt n) < worstCaseHeadComplexity n := by
  apply real_sqrt_bound_of_low_count hn hC hoverhead
  rw [lowMargin_eq_empty_of_repair hrepair, Set.ncard_empty]
  exact Nat.zero_le _

theorem real_logarithmic_bound_of_repair
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hrepair : ∀ f,
      computableWithHeadsN n
        ⌊(2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2)⌋₊ f →
      HasRelativeMargin n
        (⌈C * (⌊(2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2)⌋₊ : ℝ)⌉₊ + B) f
        (Real.exp (-Real.exp ((n : ℝ) / Real.log n)))) :
    (2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2) < worstCaseHeadComplexity n := by
  apply real_logarithmic_bound_of_low_count hn hC hoverhead
  rw [lowMargin_eq_empty_of_repair hrepair, Set.ncard_empty]
  exact Nat.zero_le _

theorem cube_le_two_pow (hn : 32 ≤ n) : n ^ 3 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      (n + 1) ^ 3 ≤ 2 * n ^ 3 := by
        have h4 : 4 ≤ n := by omega
        have hmul := Nat.mul_le_mul_right (n ^ 2) h4
        nlinarith
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

/-- A deliberately simple explicit threshold for every fixed additive overhead. -/
theorem overhead_budget_of_threshold (hn : 32 ≤ n) (hB : 500 * (B + 1) ≤ n) :
    500 * (B + 1) * n ^ 2 ≤ 2 ^ n := by
  have h := Nat.mul_le_mul_right (n ^ 2) hB
  calc
    _ ≤ n ^ 3 := by nlinarith
    _ ≤ _ := cube_le_two_pow hn

#print axioms worstCase_gt_sqrt_of_repair
#print axioms worstCase_gt_logarithmic_of_repair
#print axioms real_sqrt_bound_of_low_count
#print axioms real_logarithmic_bound_of_low_count
#print axioms real_sqrt_bound_of_repair
#print axioms real_logarithmic_bound_of_repair

end HeadComplexity.ConditionalMarginLowerBounds
