import HeadComplexity.Research.WeightedNormalizedCounting

set_option linter.style.header false

/-!
An unrestricted almost-all consequence at the quadratic-denominator scale.
This sharpens the leading constant in the distributional statement; it does
not cross the scale requested by the research benchmark.
-/

noncomputable section
namespace HeadComplexity.QuadraticScaleTypicalComplexity

variable {n H : ℕ}

/-- A finite original-model count with an explicit lower-order entropy term. -/
theorem card_le_exp_at_quadratic_budget (hn : 8 ≤ n) (hH : 0 < H)
    {u : ℝ} (hu : u ≤ 1)
    (hbudget : (n : ℝ) ^ 2 * H ≤ u * (2 : ℝ) ^ n) :
    ((headComputableFunctions n H).ncard : ℝ) ≤
      Real.exp ((u + 10 / (n : ℝ)) * (2 : ℝ) ^ n * Real.log 2) := by
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have hdimR : 2 * (n : ℝ) * H ≤ (2 : ℝ) ^ n := by
    have hh := hbudget.trans (mul_le_mul_of_nonneg_right hu hN.le)
    nlinarith
  have hdim : 2 * n * H ≤ 2 ^ n := by exact_mod_cast hdimR
  have hc := WeightedNormalizedCounting.card_le (by omega : 0 < n) hH hdim
  let U : ℝ := (n : ℝ) ^ 2 * H / (2 : ℝ) ^ n
  let C : ℝ := 16 * (Real.exp 1) ^ 2
  let B : ℝ := C * (2 : ℝ) ^ n / U
  have hUp : 0 < U := by dsimp [U]; positivity
  have hUu : U ≤ u := (div_le_iff₀ hN).mpr hbudget
  have hU1 : U ≤ 1 := hUu.trans hu
  have hCp : 0 < C := by dsimp [C]; positivity
  have hBp : 0 < B := by dsimp [B]; positivity
  have hB : B = 16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 /
      ((n : ℝ) ^ 2 * H) := by
    dsimp [B, C, U]
    field_simp
  have hlogC : Real.log C ≤ 5 := by
    have hl2 : Real.log (2 : ℝ) ≤ 3 / 4 := Real.log_two_lt_d9.le.trans (by norm_num)
    dsimp [C]
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (by positivity),
      Real.log_pow, Real.log_exp,
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlogU : -(U * Real.log U) ≤ 1 - U := by
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hUp)
    rw [Real.log_inv] at hh
    have hm := mul_le_mul_of_nonneg_left hh hUp.le
    have hi : U * U⁻¹ = 1 := mul_inv_cancel₀ hUp.ne'
    nlinarith
  have hsmall : U * (Real.log C - Real.log U) ≤ 5 := by
    have hh := mul_le_mul_of_nonneg_left hlogC hUp.le
    nlinarith
  have hlogB : Real.log B = Real.log C + (n : ℝ) * Real.log 2 - Real.log U := by
    dsimp [B]
    rw [Real.log_div (mul_pos hCp hN).ne' hUp.ne',
      Real.log_mul hCp.ne' hN.ne', Real.log_pow]
  have hscale : (n : ℝ) * H = U * (2 : ℝ) ^ n / n := by
    dsimp [U]
    field_simp
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hnN : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.le_of_lt (show n < 2 ^ n from Nat.lt_two_pow_self))
  have hNdiv : (1 : ℝ) ≤ (2 : ℝ) ^ n / n :=
    (le_div_iff₀ hnpos).mpr (by simpa using hnN)
  have hentropy : Real.log 2 + (n : ℝ) * H * Real.log B ≤
      (u + 10 / (n : ℝ)) * (2 : ℝ) ^ n * Real.log 2 := by
    have hmain := mul_le_mul_of_nonneg_right hUu (mul_pos hN hl2).le
    have hrem := mul_le_mul_of_nonneg_left hsmall (div_pos hN hnpos).le
    have hconst := mul_le_mul_of_nonneg_right hNdiv hl2.le
    have hnumerical : 5 + Real.log (2 : ℝ) ≤ 10 * Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have hlast := mul_le_mul_of_nonneg_left hnumerical (div_pos hN hnpos).le
    rw [hscale, hlogB]
    have hid : U * (2 : ℝ) ^ n / n *
        (Real.log C + (n : ℝ) * Real.log 2 - Real.log U) =
        U * ((2 : ℝ) ^ n * Real.log 2) +
          ((2 : ℝ) ^ n / n) * (U * (Real.log C - Real.log U)) := by
      field_simp
      ring
    rw [hid]
    have hout : (u + 10 / (n : ℝ)) * (2 : ℝ) ^ n * Real.log 2 =
        u * ((2 : ℝ) ^ n * Real.log 2) +
          ((2 : ℝ) ^ n / n) * (10 * Real.log 2) := by ring
    rw [hout]
    nlinarith
  calc
    _ ≤ 2 * B ^ (n * H) := by simpa only [hB] using hc
    _ = Real.exp (Real.log 2 + (n : ℝ) * H * Real.log B) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        ← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hBp]
    _ ≤ _ := Real.exp_le_exp.mpr hentropy

/-- Below any fixed constant less than one, the representable tables occupy
an exponentially small fraction of all Boolean tables, eventually. -/
theorem card_le_exp_one_sub_epsilon (hn : 8 ≤ n) (hH : 0 < H)
    {ε : ℝ} (hε : 0 < ε) (hthreshold : 20 ≤ ε * n)
    (hbudget : (n : ℝ) ^ 2 * H ≤ (1 - ε) * (2 : ℝ) ^ n) :
    ((headComputableFunctions n H).ncard : ℝ) ≤
      Real.exp ((1 - ε / 2) * (2 : ℝ) ^ n * Real.log 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : 10 / (n : ℝ) ≤ ε / 2 :=
    (div_le_iff₀ hnR).mpr (by linarith)
  apply (card_le_exp_at_quadratic_budget hn hH (by linarith : 1 - ε ≤ 1) hbudget).trans
  apply Real.exp_le_exp.mpr
  gcongr
  linarith

end HeadComplexity.QuadraticScaleTypicalComplexity
