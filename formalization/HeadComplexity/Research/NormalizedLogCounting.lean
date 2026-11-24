import HeadComplexity.Research.NormalizedCounting

set_option linter.style.header false

/-!
An exact logarithmic consequence of normalized unrestricted counting.
The original worst-case complexity and admissibility definitions are unchanged.
This sharpens the finite denominator, not its asymptotic exponent.
-/

namespace HeadComplexity.NormalizedLogCounting

open NormalizedCounting

/-- At the original worst-case width, every Boolean table is computable. -/
theorem card_at_worstCase (n : ℕ) :
    (headComputableFunctions n (worstCaseHeadComplexity n)).ncard = 2 ^ (2 ^ n) := by
  have hset : headComputableFunctions n (worstCaseHeadComplexity n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro f
    exact computableWithHeadsN_mono (HStar_le_worstCaseHeadComplexity f) (HStar_computable f)
  rw [hset, Set.ncard_univ, Nat.card_eq_fintype_card, card_all_booleanFunctions]

/-- A real inequality retaining the logarithm of the normalized Warren base. -/
theorem entropy_at_worstCase {n : ℕ} (hn : 8 ≤ n) :
    ((2 : ℝ) ^ n - 1) * Real.log 2 ≤
      (2 * (n : ℝ) * (worstCaseHeadComplexity n : ℝ)) *
        Real.log (2 * Real.exp 1 * (2 : ℝ) ^ n / n) := by
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hN : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hbase : 2 ≤ 2 * Real.exp 1 * (2 : ℝ) ^ n / n := by
    apply (le_div_iff₀ hnreal).mpr
    have h := mul_le_mul_of_nonneg_left he (show 0 ≤ (2 : ℝ) ^ n by positivity)
    nlinarith
  have hbasepos : 0 < 2 * Real.exp 1 * (2 : ℝ) ^ n / n := by positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (2 * Real.exp 1 * (2 : ℝ) ^ n / n) :=
    Real.log_le_log (by norm_num) hbase
  have hW : 0 < worstCaseHeadComplexity n := by
    exact (Nat.zero_le _).trans_lt (worstCase_gt_div_all_large hn)
  by_cases hp : 2 * n * worstCaseHeadComplexity n ≤ 2 ^ n
  · have hc := card_le hnpos hW hp
    rw [card_at_worstCase] at hc
    have hc' : (2 : ℝ) ^ (2 ^ n) ≤
        2 * (2 * Real.exp 1 * (2 : ℝ) ^ n / n) ^ (2 * n * worstCaseHeadComplexity n) := by
      exact_mod_cast hc
    have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ (2 ^ n)) hc'
    rw [Real.log_mul (by norm_num) (pow_pos hbasepos _).ne', Real.log_pow,
      Real.log_pow] at hl
    push_cast at hl
    nlinarith
  · have hp' : (2 : ℝ) ^ n ≤ 2 * (n : ℝ) * (worstCaseHeadComplexity n : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hp))
    have hmul := mul_le_mul hp' hlog hlog2.le
      (show 0 ≤ 2 * (n : ℝ) * (worstCaseHeadComplexity n : ℝ) by positivity)
    nlinarith

/-- The exact finite real lower bound obtained from normalized Warren counting.
It is unconditional but remains of order `2^n / n^2`. -/
theorem worstCase_real_log_lower {n : ℕ} (hn : 8 ≤ n) :
    (((2 : ℝ) ^ n - 1) * Real.log 2) /
      (2 * (n : ℝ) * Real.log (2 * Real.exp 1 * (2 : ℝ) ^ n / n)) ≤
        (worstCaseHeadComplexity n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hbase : 1 < 2 * Real.exp 1 * (2 : ℝ) ^ n / n := by
    apply (lt_div_iff₀ hnpos).mpr
    have h := mul_le_mul_of_nonneg_left he (show 0 ≤ (2 : ℝ) ^ n by positivity)
    nlinarith
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hnpos) (Real.log_pos hbase))).mpr
  have h := entropy_at_worstCase hn
  nlinarith

end HeadComplexity.NormalizedLogCounting
