import HeadComplexity.Research.WeightedNormalizedCounting

set_option linter.style.header false

/-!
One further substitution into the unrestricted weighted entropy inequality.
The lower bound remains of order `2^n / n^2`; no margin hypothesis is used.
-/

noncomputable section
namespace HeadComplexity.BootstrapWeightedCounting
open WeightedNormalizedCounting

variable {n : ℕ}

def refinedBase (n : ℕ) : ℝ :=
  16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 * ((n : ℝ) + 8) /
    ((n : ℝ) * ((2 : ℝ) ^ n - 1))

theorem refinedBase_factorization (_hn : 0 < n) :
    refinedBase n = (2 : ℝ) ^ n * (16 * (Real.exp 1) ^ 2) *
      (((n : ℝ) + 8) / n) * ((2 : ℝ) ^ n / ((2 : ℝ) ^ n - 1)) := by
  unfold refinedBase
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem weighted_base_le_refinedBase (hn : 8 ≤ n) :
    16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 /
      ((n : ℝ) ^ 2 * (worstCaseHeadComplexity n : ℝ)) ≤ refinedBase n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : (1 : ℝ) < (2 : ℝ) ^ n := one_lt_pow₀ (by norm_num) (by omega)
  have hw := WeightedNormalizedCounting.worstCase_real_lower hn
  have hden : 0 < (n : ℝ) * (n + 8) := by positivity
  have hmul := (div_le_iff₀ hden).mp hw
  have hd : (n : ℝ) * ((2 : ℝ) ^ n - 1) / (n + 8) ≤
      (n : ℝ) ^ 2 * (worstCaseHeadComplexity n : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 8)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmul hnR.le]
  have hh := div_le_div_of_nonneg_left
    (show 0 ≤ 16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 by positivity)
    (show 0 < (n : ℝ) * ((2 : ℝ) ^ n - 1) / (n + 8) by positivity) hd
  calc
    _ ≤ _ := hh
    _ = refinedBase n := by unfold refinedBase; field_simp

theorem refinedBase_ge_four (hn : 8 ≤ n) : 4 ≤ refinedBase n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
      (show 1 ≤ n by omega))
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have he2 : (16 : ℝ) ≤ 16 * (Real.exp 1) ^ 2 := by nlinarith
  have hnratio : (1 : ℝ) ≤ ((n : ℝ) + 8) / n :=
    (le_div_iff₀ hnR).mpr (by linarith)
  have hNratio : (1 : ℝ) ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 1) :=
    (le_div_iff₀ (by linarith)).mpr (by linarith)
  rw [refinedBase_factorization (by omega)]
  calc
    (4 : ℝ) ≤ 2 * 16 * 1 * 1 := by norm_num
    _ ≤ _ := by gcongr

theorem refined_entropy_at_worstCase (hn : 8 ≤ n) :
    ((2 : ℝ) ^ n - 1) * Real.log 2 ≤
      (n : ℝ) * (worstCaseHeadComplexity n : ℝ) * Real.log (refinedBase n) :=
  entropy_at_worstCase_of_base hn _ (refinedBase_ge_four hn)
    (weighted_base_le_refinedBase hn)

/-- A stronger explicit logarithmic-denominator lower bound after one
bootstrap, against the unchanged unrestricted worst-case definition. -/
theorem worstCase_real_log_lower (hn : 8 ≤ n) :
    (((2 : ℝ) ^ n - 1) * Real.log 2) / ((n : ℝ) * Real.log (refinedBase n)) ≤
      (worstCaseHeadComplexity n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (refinedBase n) := Real.log_pos (by
    have := refinedBase_ge_four hn; linarith)
  apply (div_le_iff₀ (mul_pos hnR hlog)).mpr
  have hh := refined_entropy_at_worstCase hn
  nlinarith

theorem refinedBase_le_two_pow (hn : 256 ≤ n) :
    refinedBase n ≤ (2 : ℝ) ^ (n + 7) := by
  have hnR : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : (256 : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
      (show 8 ≤ n by omega))
  have he : Real.exp (1 : ℝ) ≤ 11 / 4 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hep : 0 ≤ Real.exp (1 : ℝ) := (Real.exp_pos _).le
  have he2 : 16 * (Real.exp 1) ^ 2 ≤ 121 := by nlinarith
  have hnratio : ((n : ℝ) + 8) / n ≤ 33 / 32 :=
    (div_le_iff₀ hnpos).mpr (by linarith)
  have hNratio : (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 1) ≤ 256 / 255 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hNratio0 : 0 ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 1) :=
    (div_pos (by positivity) (by linarith)).le
  rw [refinedBase_factorization (by omega), pow_add]
  calc
    _ ≤ (2 : ℝ) ^ n * 121 * (33 / 32) * (256 / 255) := by gcongr
    _ ≤ (2 : ℝ) ^ n * 2 ^ 7 := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]

/-- The bootstrapped finite constant is seven for all `n≥256`. This still
has a quadratic denominator and does not prove a power or logarithmic gain. -/
theorem worstCase_real_lower (hn : 256 ≤ n) :
    ((2 : ℝ) ^ n - 1) / ((n : ℝ) * (n + 7)) ≤ (worstCaseHeadComplexity n : ℝ) := by
  have hn8 : 8 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbasepos : 0 < refinedBase n := by have := refinedBase_ge_four hn8; linarith
  have hl := Real.log_le_log hbasepos (refinedBase_le_two_pow hn)
  rw [Real.log_pow] at hl
  push_cast at hl
  have hw := refined_entropy_at_worstCase hn8
  have hh := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ (n : ℝ) * (worstCaseHeadComplexity n : ℝ) by positivity)
  have hcancel : (2 : ℝ) ^ n - 1 ≤ (n : ℝ) * (n + 7) * (worstCaseHeadComplexity n : ℝ) := by
    nlinarith
  apply (div_le_iff₀ (show 0 < (n : ℝ) * (n + 7) by positivity)).mpr
  nlinarith

/-- An explicit approach to leading constant one. This is a consequence of
the finite bound, not an improvement of its quadratic denominator. -/
theorem worstCase_real_leading_constant (hn : 256 ≤ n) :
    (1 - 8 / (n : ℝ)) * (2 : ℝ) ^ n / (n : ℝ) ^ 2 ≤
      (worstCaseHeadComplexity n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.le_of_lt (show n < 2 ^ n from Nat.lt_two_pow_self))
  have hNpos : 0 < (2 : ℝ) ^ n := by positivity
  have hcompare : (1 - 8 / (n : ℝ)) * (2 : ℝ) ^ n / (n : ℝ) ^ 2 ≤
      ((2 : ℝ) ^ n - 1) / ((n : ℝ) * (n + 7)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hnR) (by positivity)).mpr
    have hmul := mul_le_mul_of_nonneg_right hN hnR.le
    field_simp
    nlinarith
  exact hcompare.trans (worstCase_real_lower hn)

/-- Every fixed constant below one is an eventual unrestricted lower-bound
constant. The explicit sufficient threshold is `n ≥ max 256 (8 / ε)`. -/
theorem worstCase_real_one_sub_epsilon {ε : ℝ} (hn : 256 ≤ n)
    (_hε : 0 < ε) (hthreshold : 8 ≤ ε * n) :
    (1 - ε) * (2 : ℝ) ^ n / (n : ℝ) ^ 2 ≤
      (worstCaseHeadComplexity n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have heps : 8 / (n : ℝ) ≤ ε := (div_le_iff₀ hnR).mpr hthreshold
  apply le_trans _ (worstCase_real_leading_constant hn)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 1 - ε ≤ 1 - 8 / (n : ℝ))
      (by positivity)) (by positivity)

/-- The leading constant one is approached along all sufficiently large input
dimensions, against the original unrestricted worst-case definition. -/
theorem worstCase_eventually_one_sub_epsilon {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 - ε) * (2 : ℝ) ^ n / (n : ℝ) ^ 2 ≤
        (worstCaseHeadComplexity n : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 256 ⌈8 / ε⌉₊)] with n hn
  have hn256 : 256 ≤ n := (le_max_left _ _).trans hn
  have hnceil : ⌈8 / ε⌉₊ ≤ n := (le_max_right _ _).trans hn
  have hratio : 8 / ε ≤ (n : ℝ) :=
    (Nat.le_ceil (8 / ε)).trans (by exact_mod_cast hnceil)
  apply worstCase_real_one_sub_epsilon hn256 hε
  have hh := (div_le_iff₀ hε).mp hratio
  linarith

end HeadComplexity.BootstrapWeightedCounting
