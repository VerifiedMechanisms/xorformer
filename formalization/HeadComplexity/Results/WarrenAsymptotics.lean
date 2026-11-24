import HeadComplexity.Results.WarrenBound
import Mathlib.Analysis.Asymptotics.Defs

set_option linter.style.header false

/-!
# Explicit unconditional quadratic-denominator lower bound

This records the asymptotic content of the checked Warren count. It is weaker
than the requested matching lower bound with a single factor of the dimension.
The original model and both complexity definitions are unchanged.
-/

namespace HeadComplexity

open Filter Asymptotics

theorem seventy_mul_square_le_two_pow {n : ℕ} (hn : 16 ≤ n) :
    70 * n * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 n]
    have hstep : 70 * (n + 1) * (n + 1) ≤ 2 * (70 * n * n) := by
      nlinarith
    nlinarith

/-- A concrete real-valued unconditional lower bound, valid from dimension 16.
This is an inverse-square saving and does not establish the matching target. -/
theorem worstCaseHeadComplexity_real_ge_two_pow_div_seventy_square
    {n : ℕ} (hn : 16 ≤ n) :
    (2 : ℝ) ^ n / (70 * (n : ℝ) ^ 2) ≤ worstCaseHeadComplexity n := by
  have hn1 : 1 ≤ n := by omega
  have hden : 0 < 35 * n * n := by positivity
  have hpow := seventy_mul_square_le_two_pow hn
  have hsize : 35 * n * n ≤ 2 ^ n - 1 := by
    have : 2 ≤ 35 * n * n := by nlinarith
    have : 35 * n * n + 1 ≤ 2 ^ n := by nlinarith
    omega
  have hnat := (Nat.div_lt_iff_lt_mul hden).mp
    (worstCaseHeadComplexity_gt_div hn1 hsize)
  have hone : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hreal : (2 : ℝ) ^ n - 1 <
      (worstCaseHeadComplexity n : ℝ) * (35 * n * n) := by
    exact_mod_cast hnat
  have hpow2 : (2 : ℝ) ≤ 2 ^ n := by
    exact_mod_cast (show 2 ≤ 2 ^ n by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 70 * (n : ℝ) ^ 2)).mpr
  nlinarith

/-- The fully checked counting baseline is `Omega(2^n / n^2)`. -/
theorem two_pow_div_square_isBigO_worstCaseHeadComplexity :
    (fun n : ℕ ↦ (2 : ℝ) ^ n / (n : ℝ) ^ 2) =O[atTop]
      (fun n : ℕ ↦ (worstCaseHeadComplexity n : ℝ)) := by
  apply IsBigO.of_bound 70
  filter_upwards [eventually_ge_atTop 16] with n hn
  have h := worstCaseHeadComplexity_real_ge_two_pow_div_seventy_square hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n / (n : ℝ) ^ 2),
    abs_of_nonneg (Nat.cast_nonneg _)]
  have h' := (div_le_iff₀ (by positivity : (0 : ℝ) < 70 * (n : ℝ) ^ 2)).mp h
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).mpr
  nlinarith

end HeadComplexity
