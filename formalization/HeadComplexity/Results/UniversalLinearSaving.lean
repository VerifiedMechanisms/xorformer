import HeadComplexity.Results.StarCoverRecursion

set_option linter.style.header false

/-!
# Universal head complexity with a linear denominator

Balanced block recursion discounts repairs by the density of a smaller
cover. The rate `7/(2*m)` and the checked inequality
`exp(-7/4) ≤ 7/40` close strong induction with the absolute constant 11.
-/

namespace HeadComplexity

open Finset
open scoped BigOperators

private theorem exp_neg_seven_quarters_le : Real.exp (-(7 / 4 : ℝ)) ≤ (7 / 40 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hbound : (40 / 7 : ℝ) ≤ Real.exp (7 / 4) := by linarith
  rw [Real.exp_neg]
  have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 40 / 7) hbound
  norm_num [one_div] at this ⊢
  exact this

private theorem failure_sum_le_exponential (m : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hpone : p ≤ 1) :
    (1 - p) * (2 - p) ^ m ≤ (2 : ℝ) ^ m * Real.exp (-(m : ℝ) * p / 2) := by
  have h := bernoulliStarBudget_le_exponential m p hp hpone
  dsimp [bernoulliStarBudget] at h
  nlinarith

/-- A uniform asymmetric monomial star cover needs at most
`11 * 2^n / n` centers. This is a real bound on an actual finite cover. -/
theorem monomialStarCoverNumber_real_le_eleven (n : ℕ) (hn : 0 < n) :
    (monomialStarCoverNumber n : ℝ) ≤ 11 * (2 : ℝ) ^ n / n := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    by_cases hsmall : n < 74
    · by_cases hn1 : n = 1
      · subst n
        have hhalf := monomialStarCoverNumber_le_half (n := 1) (by decide)
        norm_num at hhalf ⊢
        exact_mod_cast hhalf.trans (by decide : 1 ≤ 22)
      · have hn2 : 2 ≤ n := by omega
        have hlogtwo : Real.log 2 ≤ (3 / 4 : ℝ) := by linarith [Real.log_two_lt_d9]
        have hlogsixtyfour : Real.log 64 = 6 * Real.log 2 := by
          rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
          norm_num
        have hnle : (n : ℝ) ≤ 128 := by exact_mod_cast (show n ≤ 128 by omega)
        have hlogle := Real.log_le_log
          (by positivity : (0 : ℝ) < (n : ℝ) / 2) (by linarith : (n : ℝ) / 2 ≤ 64)
        have hcoeff : 2 * (Real.log ((n : ℝ) / 2) + 1) ≤ 11 := by
          rw [hlogsixtyfour] at hlogle
          linarith
        calc
          (monomialStarCoverNumber n : ℝ) ≤ logarithmicStarBudget n :=
            monomialStarCoverNumber_real_le_logarithmic hn2
          _ ≤ 11 * (2 : ℝ) ^ n / n := by
            dsimp [logarithmicStarBudget]
            apply (div_le_div_iff_of_pos_right hnpos).mpr
            have hscaled := mul_le_mul_of_nonneg_right hcoeff
              (by positivity : (0 : ℝ) ≤ 2 ^ n)
            nlinarith
    · let m := n / 2
      let r := n - m
      have hmten : 37 ≤ m := by dsimp [m]; omega
      have hm : 0 < m := by omega
      have hmr : m ≤ r := by dsimp [m, r]; omega
      have hr : 0 < r := by omega
      have hrlt : r < n := by dsimp [r]; omega
      have hadd : m + r = n := by dsimp [m, r]; omega
      have hnupper : n ≤ 2 * m + 1 := by dsimp [m]; omega
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
      have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
      have hmrReal : (m : ℝ) ≤ r := by exact_mod_cast hmr
      let p : ℝ := 7 / (2 * m)
      have hp : 0 ≤ p := by dsimp [p]; positivity
      have hpone : p ≤ 1 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).mpr
        simp only [one_mul]
        exact_mod_cast (show 7 ≤ 2 * m by omega)
      have hrec := monomialStarCoverNumber_block_recurrence m r p hp hpone
      rw [hadd] at hrec
      have hkr : (monomialStarCoverNumber r : ℝ) ≤ 11 * (2 : ℝ) ^ r / m := by
        calc
          (monomialStarCoverNumber r : ℝ) ≤ 11 * (2 : ℝ) ^ r / r := ih r hrlt hr
          _ ≤ 11 * (2 : ℝ) ^ r / m := by gcongr
      have hfailure : (1 - p) * (2 - p) ^ m ≤ 7 * (2 : ℝ) ^ m / 40 := by
        have h := failure_sum_le_exponential m p hp hpone
        have heq : -(m : ℝ) * p / 2 = -(7 / 4 : ℝ) := by
          dsimp [p]
          field_simp
          norm_num
        rw [heq] at h
        calc
          (1 - p) * (2 - p) ^ m ≤ (2 : ℝ) ^ m * Real.exp (-(7 / 4 : ℝ)) := h
          _ ≤ (2 : ℝ) ^ m * (7 / 40 : ℝ) :=
            mul_le_mul_of_nonneg_left exp_neg_seven_quarters_le (by positivity)
          _ = 7 * (2 : ℝ) ^ m / 40 := by ring
      have hfailnonneg : 0 ≤ (1 - p) * (2 - p) ^ m := by
        apply mul_nonneg (by linarith)
        exact pow_nonneg (by linarith) _
      have hproduct := mul_le_mul hkr hfailure hfailnonneg
        (by positivity : (0 : ℝ) ≤ 11 * (2 : ℝ) ^ r / m)
      have hgeom : (2 : ℝ) ^ n = (2 : ℝ) ^ m * (2 : ℝ) ^ r := by
        rw [← pow_add, hadd]
      have hfrac : (217 : ℝ) / (40 * m) ≤ 11 / (n : ℝ) := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 40 * m) hnpos).mpr
        have hmtenReal : (37 : ℝ) ≤ m := by exact_mod_cast hmten
        have hnupperReal : (n : ℝ) ≤ 2 * m + 1 := by exact_mod_cast hnupper
        nlinarith
      calc
        (monomialStarCoverNumber n : ℝ) ≤ (2 : ℝ) ^ n * p +
            monomialStarCoverNumber r * ((1 - p) * (2 - p) ^ m) := by
          simpa only [mul_assoc] using hrec
        _ ≤ (2 : ℝ) ^ n * p + (11 * (2 : ℝ) ^ r / m) * (7 * (2 : ℝ) ^ m / 40) :=
          add_le_add le_rfl hproduct
        _ = (2 : ℝ) ^ n * (217 / (40 * m)) := by
          dsimp [p]
          rw [hgeom]
          field_simp
          ring
        _ ≤ (2 : ℝ) ^ n * (11 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = 11 * (2 : ℝ) ^ n / n := by ring

/-- Compatibility form of the first linear-saving constant. -/
theorem monomialStarCoverNumber_real_le_twelve (n : ℕ) (hn : 0 < n) :
    (monomialStarCoverNumber n : ℝ) ≤ 12 * (2 : ℝ) ^ n / n :=
  (monomialStarCoverNumber_real_le_eleven n hn).trans (by gcongr; norm_num)

/-- The sharper constant 11 applies to every actual attention function. -/
theorem HStar_real_le_eleven_mul_two_pow_div {n : ℕ} (hn : 0 < n)
    (f : (Fin n → Bool) → Bool) :
    (HStar n f : ℝ) ≤ 11 * (2 : ℝ) ^ n / n :=
  (by exact_mod_cast HStar_le_monomialStarCoverNumber f :
    (HStar n f : ℝ) ≤ monomialStarCoverNumber n).trans
      (monomialStarCoverNumber_real_le_eleven n hn)

/-- Universal attention head bound with a linear saving in input count. -/
theorem HStar_real_le_twelve_mul_two_pow_div {n : ℕ} (hn : 0 < n)
    (f : (Fin n → Bool) → Bool) :
    (HStar n f : ℝ) ≤ 12 * (2 : ℝ) ^ n / n :=
  (by exact_mod_cast HStar_le_monomialStarCoverNumber f :
    (HStar n f : ℝ) ≤ monomialStarCoverNumber n).trans
      (monomialStarCoverNumber_real_le_twelve n hn)

/-- The final universal budget retains all previous bounds and adds the
linear-denominator estimate. Real division makes its zero endpoint zero. -/
noncomputable def universalLinearStarBound (n : ℕ) : ℕ :=
  min (universalStarBound n) ⌊12 * (2 : ℝ) ^ n / n⌋₊

/-- Unconditional joint universal head bound, including dimension zero. -/
theorem HStar_le_universalLinearStarBound {n : ℕ}
    (f : (Fin n → Bool) → Bool) : HStar n f ≤ universalLinearStarBound n := by
  apply Nat.le_min.mpr
  refine ⟨HStar_le_universalStarBound f, ?_⟩
  by_cases hn : 0 < n
  · exact Nat.le_floor (HStar_real_le_twelve_mul_two_pow_div hn f)
  · have hnzero : n = 0 := by omega
    have h := HStar_le_universal_boolean f
    simpa [hnzero] using h

/-- Worst-case presentation of the same universal linear saving. -/
theorem worstCaseHeadComplexity_real_le_twelve_mul_two_pow_div
    {n : ℕ} (hn : 0 < n) :
    (worstCaseHeadComplexity n : ℝ) ≤ 12 * (2 : ℝ) ^ n / n := by
  have hnat : worstCaseHeadComplexity n ≤ ⌊12 * (2 : ℝ) ^ n / n⌋₊ := by
    apply Finset.sup_le
    intro f _
    exact Nat.le_floor (HStar_real_le_twelve_mul_two_pow_div hn f)
  exact (by exact_mod_cast hnat : (worstCaseHeadComplexity n : ℝ) ≤
    ⌊12 * (2 : ℝ) ^ n / n⌋₊).trans (Nat.floor_le (by positivity))

/-- Retain every earlier endpoint and add the sharper constant 11. -/
noncomputable def universalElevenStarBound (n : ℕ) : ℕ :=
  min (universalLinearStarBound n) ⌊11 * (2 : ℝ) ^ n / n⌋₊

theorem HStar_le_universalElevenStarBound {n : ℕ}
    (f : (Fin n → Bool) → Bool) : HStar n f ≤ universalElevenStarBound n := by
  apply Nat.le_min.mpr
  refine ⟨HStar_le_universalLinearStarBound f, ?_⟩
  by_cases hn : 0 < n
  · exact Nat.le_floor (HStar_real_le_eleven_mul_two_pow_div hn f)
  · have hnzero : n = 0 := by omega
    have h := HStar_le_universal_boolean f
    simpa [hnzero] using h

/-- Worst-case form of the sharpest proved absolute constant. -/
theorem worstCaseHeadComplexity_real_le_eleven_mul_two_pow_div
    {n : ℕ} (hn : 0 < n) :
    (worstCaseHeadComplexity n : ℝ) ≤ 11 * (2 : ℝ) ^ n / n := by
  have hnat : worstCaseHeadComplexity n ≤ ⌊11 * (2 : ℝ) ^ n / n⌋₊ := by
    apply Finset.sup_le
    intro f _
    exact Nat.le_floor (HStar_real_le_eleven_mul_two_pow_div hn f)
  exact (by exact_mod_cast hnat : (worstCaseHeadComplexity n : ℝ) ≤
    ⌊11 * (2 : ℝ) ^ n / n⌋₊).trans (Nat.floor_le (by positivity))

/-- Scale out the input-count and truth-table factors with an exact bridge. -/
theorem normalized_HStar_le_eleven {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    (n : ℝ) * HStar n f / (2 : ℝ) ^ n ≤ 11 := by
  by_cases hn : 0 < n
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have h := (le_div_iff₀ hnpos).mp (HStar_real_le_eleven_mul_two_pow_div hn f)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
    nlinarith
  · have hnzero : n = 0 := by omega
    simp [hnzero]

/-- The final natural budget preserves every logarithmic endpoint. -/
theorem universalElevenStarBound_le_logarithmic (n : ℕ) :
    universalElevenStarBound n ≤ universalStarBound n :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- The constant 11 is strictly smaller than the old logarithmic coefficient
in every dimension at least 256. -/
theorem eleven_lt_logarithmic_coefficient {n : ℕ} (hn : 256 ≤ n) :
    (11 : ℝ) < 2 * (Real.log ((n : ℝ) / 2) + 1) := by
  have hnreal : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogtwo : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 128)
    (by linarith : (128 : ℝ) ≤ (n : ℝ) / 2)
  rw [hlog128] at hmono
  linarith

/-- Strict comparison of the actual unnormalized applicable real budgets. -/
theorem eleven_budget_lt_logarithmic {n : ℕ} (hn : 256 ≤ n) :
    11 * (2 : ℝ) ^ n / n < logarithmicStarBudget n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := mul_lt_mul_of_pos_right (eleven_lt_logarithmic_coefficient hn)
    (by positivity : (0 : ℝ) < 2 ^ n)
  apply (div_lt_div_iff_of_pos_right hnpos).mpr
  nlinarith

end HeadComplexity
