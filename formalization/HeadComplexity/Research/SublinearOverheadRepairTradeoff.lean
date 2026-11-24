import HeadComplexity.Research.ConditionalMarginLowerBounds

set_option linter.style.header false

/-!
A stronger margin permits a nonconstant head overhead. These are exact
conditional implications against the original model, not repair theorems.
-/

noncomputable section
namespace HeadComplexity.SublinearOverheadRepairTradeoff

open RelativeMarginQuantifiers MarginCapacityEstimates ConditionalMarginLowerBounds

variable {n H B : ℕ} {C : ℝ}

/-- The smallest parameter admitted by the finite entropy estimate corresponds
exactly to the singly exponential margin `exp (-(n+1))`. -/
theorem testMargin_log_dimension :
    testMargin (Real.log ((n : ℝ) + 1)) = Real.exp (-((n : ℝ) + 1)) := by
  unfold testMargin
  rw [Real.exp_log (by positivity)]

theorem log_dimension_range : Real.log ((n : ℝ) + 1) ≤ n := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
  linarith

/-- At this stronger margin, the finite count allows width proportional to
`N/(n log(n+1))`; the overhead `C` may depend on the dimension. -/
theorem card_highMargin_linear_exponent_overhead
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n /
      (100 * C * n * Real.log ((n : ℝ) + 1))) :
    (highMarginFunctions n (⌈C * (H : ℝ)⌉₊ + B)
      (Real.exp (-((n : ℝ) + 1)))).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  rw [← testMargin_log_dimension]
  apply card_highMargin_test_with_overhead hn hC le_rfl log_dimension_range
    hoverhead hwidth
  push_cast
  have hceil : (⌈C * (H : ℝ)⌉₊ : ℝ) < C * (H : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  linarith

/-- A repair with dimension-dependent overhead and singly exponential margin
would imply a corresponding unrestricted lower bound. The repair is an
explicit hypothesis over every narrow truth table. -/
theorem worstCase_gt_of_linear_exponent_repair
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n /
      (100 * C * n * Real.log ((n : ℝ) + 1)))
    (hrepair : ∀ f, computableWithHeadsN n H f →
      HasRelativeMargin n (⌈C * (H : ℝ)⌉₊ + B) f
        (Real.exp (-((n : ℝ) + 1)))) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_repair_and_half_count (by omega)
    (card_highMargin_linear_exponent_overhead hn hC hoverhead hwidth) hrepair

/-- The same tradeoff can instead be supplied by an upper count of the
universally low-margin exceptional truth tables. -/
theorem worstCase_gt_of_linear_exponent_low_count
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n /
      (100 * C * n * Real.log ((n : ℝ) + 1)))
    (hlow : (allRepresentationsLowMargin n H (⌈C * (H : ℝ)⌉₊ + B)
      (Real.exp (-((n : ℝ) + 1)))).ncard ≤ 2 ^ (2 ^ (n - 1))) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_two_half_counts (by omega)
    (card_highMargin_linear_exponent_overhead hn hC hoverhead hwidth) hlow

/-- In particular square-root overhead would suffice for a power saving,
with one logarithmic loss compared with the aimed benchmark. -/
theorem worstCase_gt_of_sqrt_overhead_repair
    (hn : 32 ≤ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n /
      (100 * Real.sqrt n * n * Real.log ((n : ℝ) + 1)))
    (hrepair : ∀ f, computableWithHeadsN n H f →
      HasRelativeMargin n ⌈Real.sqrt n * (H : ℝ)⌉₊ f
        (Real.exp (-((n : ℝ) + 1)))) :
    H < worstCaseHeadComplexity n := by
  have hroot : 1 ≤ Real.sqrt (n : ℝ) := by
    exact Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n by omega))
  simpa using worstCase_gt_of_linear_exponent_repair (B := 0) hn hroot
    (by simpa using quadratic_le_two_pow hn) hwidth (by simpa using hrepair)

end HeadComplexity.SublinearOverheadRepairTradeoff
