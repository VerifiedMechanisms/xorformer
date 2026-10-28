import HeadComplexity.Results.BernoulliStarCover
import HeadComplexity.Results.UniversalStarUpperBound

set_option linter.style.header false

/-!
# Universal logarithmic head upper bounds

Finite independent selection followed by repair gives a universal bound
`2 * 2^n * (log (n/2) + 1) / n` for `n ≥ 2`. We retain all earlier
endpoints by taking their minimum. The normalized worst-case cost tends to
zero, strengthening the original geometric upper bound qualitatively.
-/

namespace HeadComplexity

open Finset Filter
open scoped BigOperators Topology

/-- Exponential relaxation of the exact finite alteration budget. -/
theorem bernoulliStarBudget_le_exponential (n : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hpone : p ≤ 1) :
    bernoulliStarBudget n p ≤
      (2 : ℝ) ^ n * (p + Real.exp (-(n : ℝ) * p / 2)) := by
  have hbase : 0 ≤ 1 - p / 2 := by linarith
  have hpow := pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg (p / 2)) n
  rw [← Real.exp_nat_mul] at hpow
  have hexponent : (n : ℝ) * -(p / 2) = -(n : ℝ) * p / 2 := by ring
  rw [hexponent] at hpow
  have hpow_nonneg : 0 ≤ (1 - p / 2) ^ n := pow_nonneg hbase n
  have hqpow : (1 - p) * (1 - p / 2) ^ n ≤ Real.exp (-(n : ℝ) * p / 2) :=
    (mul_le_of_le_one_left hpow_nonneg (by linarith)).trans hpow
  have htwo : 2 - p = 2 * (1 - p / 2) := by ring
  dsimp [bernoulliStarBudget]
  rw [htwo, mul_pow]
  have hscaled := mul_le_mul_of_nonneg_left hqpow (by positivity : (0 : ℝ) ≤ 2 ^ n)
  calc
    (2 : ℝ) ^ n * p + (1 - p) * ((2 : ℝ) ^ n * (1 - p / 2) ^ n) =
      (2 : ℝ) ^ n * p + (2 : ℝ) ^ n * ((1 - p) * (1 - p / 2) ^ n) := by ring
    _ ≤ (2 : ℝ) ^ n * p + (2 : ℝ) ^ n * Real.exp (-(n : ℝ) * p / 2) :=
      add_le_add le_rfl hscaled
    _ = (2 : ℝ) ^ n * (p + Real.exp (-(n : ℝ) * p / 2)) := by ring

/-- The rate minimizing the exponential relaxation. -/
noncomputable def logarithmicStarRate (n : ℕ) : ℝ :=
  2 * Real.log ((n : ℝ) / 2) / n

/-- The chosen rate is admissible in every dimension at least two. -/
theorem logarithmicStarRate_mem_Icc {n : ℕ} (hn : 2 ≤ n) :
    logarithmicStarRate n ∈ Set.Icc (0 : ℝ) 1 := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hxpos : (0 : ℝ) < (n : ℝ) / 2 := by positivity
  have hlog : 0 ≤ Real.log ((n : ℝ) / 2) := Real.log_nonneg (by linarith)
  have hlogle := Real.log_le_sub_one_of_pos hxpos
  constructor
  · dsimp [logarithmicStarRate]
    positivity
  · dsimp [logarithmicStarRate]
    apply (div_le_iff₀ hnpos).mpr
    nlinarith

/-- Explicit logarithmic head budget, with no rounding loss. -/
noncomputable def logarithmicStarBudget (n : ℕ) : ℝ :=
  2 * (2 : ℝ) ^ n * (Real.log ((n : ℝ) / 2) + 1) / n

/-- The exact alteration average is bounded by the explicit logarithmic
budget at the chosen admissible sampling rate. -/
theorem bernoulliStarBudget_logarithmic_le {n : ℕ} (hn : 2 ≤ n) :
    bernoulliStarBudget n (logarithmicStarRate n) ≤ logarithmicStarBudget n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrate := logarithmicStarRate_mem_Icc hn
  have hexponent : -(n : ℝ) * logarithmicStarRate n / 2 =
      -Real.log ((n : ℝ) / 2) := by
    dsimp [logarithmicStarRate]
    field_simp
  calc
    bernoulliStarBudget n (logarithmicStarRate n) ≤ (2 : ℝ) ^ n *
        (logarithmicStarRate n + Real.exp (-(n : ℝ) * logarithmicStarRate n / 2)) :=
      bernoulliStarBudget_le_exponential n _ hrate.1 hrate.2
    _ = logarithmicStarBudget n := by
      rw [hexponent, Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ) / 2)]
      dsimp [logarithmicStarRate, logarithmicStarBudget]
      field_simp

/-- The original universal interpolation theorem improves to a logarithmic
fraction of truth-table size, in the unchanged attention model. -/
theorem HStar_real_le_logarithmicStarBudget {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → Bool) → Bool) :
    (HStar n f : ℝ) ≤ logarithmicStarBudget n := by
  have hp := logarithmicStarRate_mem_Icc hn
  exact (HStar_real_le_bernoulliStarBudget f _ hp.1 hp.2).trans
    (bernoulliStarBudget_logarithmic_le hn)

/-- An unconditional budget preserving every endpoint of the original
universal and half-cube bounds. -/
noncomputable def universalStarBound (n : ℕ) : ℕ :=
  min (min (2 ^ n - 1) (2 ^ (n - 1)))
    (if 2 ≤ n then ⌊logarithmicStarBudget n⌋₊ else 2 ^ n - 1)

/-- Final unconditional universal upper bound. -/
theorem HStar_le_universalStarBound {n : ℕ} (f : (Fin n → Bool) → Bool) :
    HStar n f ≤ universalStarBound n := by
  apply Nat.le_min.mpr
  refine ⟨HStar_le_min_universal_star f, ?_⟩
  split
  · exact Nat.le_floor (HStar_real_le_logarithmicStarBudget ‹2 ≤ n› f)
  · exact HStar_le_universal_boolean f

/-- The final bound retains the old universal budget pointwise. -/
theorem universalStarBound_le_original (n : ℕ) : universalStarBound n ≤ 2 ^ n - 1 :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- The final bound also retains the half-cube improvement pointwise. -/
theorem universalStarBound_le_half (n : ℕ) : universalStarBound n ≤ 2 ^ (n - 1) :=
  (min_le_left _ _).trans (min_le_right _ _)

/-- The logarithmic budget is strictly below half of truth-table size in
all dimensions at least 32. -/
theorem logarithmicStarBudget_lt_half {n : ℕ} (hn : 32 ≤ n) :
    logarithmicStarBudget n < (2 : ℝ) ^ (n - 1) := by
  have hnreal : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogtwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogeight : Real.log 8 ≤ 3 := by
    have h : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [h]
    linarith
  have hlog := Real.log_le_sub_one_of_pos
    (div_pos hnpos (by norm_num : (0 : ℝ) < 16))
  rw [Real.log_div hnpos.ne' (by norm_num)] at hlog
  have hlogdiv : Real.log ((n : ℝ) / 2) ≤ 2 + (n : ℝ) / 16 := by
    have hlogratio : Real.log 16 = Real.log 8 + Real.log 2 := by
      rw [← Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    rw [Real.log_div hnpos.ne' (by norm_num)]
    linarith
  have hratio : 2 * (Real.log ((n : ℝ) / 2) + 1) / n < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ hnpos).mpr
    linarith
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = n - 1 + 1 by omega, pow_succ]
    ring
  calc
    logarithmicStarBudget n =
        (2 : ℝ) ^ n * (2 * (Real.log ((n : ℝ) / 2) + 1) / n) := by
      dsimp [logarithmicStarBudget]
      ring
    _ < (2 : ℝ) ^ n * (1 / 2 : ℝ) :=
      mul_lt_mul_of_pos_left hratio (by positivity)
    _ = (2 : ℝ) ^ (n - 1) := by rw [hpow]; ring

/-- Strict improvement of an applicable budget, uniformly for all functions
in every dimension at least 32. -/
theorem universalStarBound_lt_half {n : ℕ} (hn : 32 ≤ n) :
    universalStarBound n < 2 ^ (n - 1) := by
  have hn2 : 2 ≤ n := by omega
  have hpos : 0 ≤ logarithmicStarBudget n :=
    le_trans (by positivity : (0 : ℝ) ≤ (HStar n (fun _ ↦ false) : ℝ))
      (HStar_real_le_logarithmicStarBudget hn2 _)
  have hf : ⌊logarithmicStarBudget n⌋₊ < 2 ^ (n - 1) := by
    apply (Nat.floor_lt hpos).mpr
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using logarithmicStarBudget_lt_half hn
  have hle : universalStarBound n ≤ ⌊logarithmicStarBudget n⌋₊ := by
    simp only [universalStarBound, ite_eq_left hn2]
    exact min_le_right _ _
  exact hle.trans_lt hf

/-- Worst-case form of the logarithmic universal bound. -/
theorem worstCaseHeadComplexity_real_le_logarithmicStarBudget
    {n : ℕ} (hn : 2 ≤ n) :
    (worstCaseHeadComplexity n : ℝ) ≤ logarithmicStarBudget n := by
  have hnat : worstCaseHeadComplexity n ≤ ⌊logarithmicStarBudget n⌋₊ := by
    apply Finset.sup_le
    intro f _
    exact Nat.le_floor (HStar_real_le_logarithmicStarBudget hn f)
  have hnonneg : 0 ≤ logarithmicStarBudget n :=
    le_trans (by positivity : (0 : ℝ) ≤ (HStar n (fun _ ↦ false) : ℝ))
      (HStar_real_le_logarithmicStarBudget hn _)
  exact (by exact_mod_cast hnat : (worstCaseHeadComplexity n : ℝ) ≤
    ⌊logarithmicStarBudget n⌋₊).trans (Nat.floor_le hnonneg)

/-- Worst-case head complexity is a vanishing fraction of truth-table size. -/
theorem tendsto_worstCaseHeadComplexity_div_two_pow :
    Tendsto (fun n : ℕ ↦ (worstCaseHeadComplexity n : ℝ) / (2 : ℝ) ^ n)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ 2 * Real.log n / (n : ℝ) + 2 / (n : ℝ))
      atTop (𝓝 0) := by
    have hlog := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have h := (hlog.const_mul 2).add (hinv.const_mul 2)
    simpa [mul_div_assoc, div_eq_mul_inv, mul_assoc] using h
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ by positivity)) ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogle : Real.log ((n : ℝ) / 2) ≤ Real.log n :=
    Real.log_le_log (by positivity) (by linarith)
  have hbound := worstCaseHeadComplexity_real_le_logarithmicStarBudget hn
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
  calc
    (worstCaseHeadComplexity n : ℝ) ≤ logarithmicStarBudget n := hbound
    _ ≤ (2 * Real.log n / (n : ℝ) + 2 / (n : ℝ)) * (2 : ℝ) ^ n := by
      dsimp [logarithmicStarBudget]
      have hmul := mul_le_mul_of_nonneg_left hlogle
        (by positivity : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ n / n)
      calc
        2 * (2 : ℝ) ^ n * (Real.log ((n : ℝ) / 2) + 1) / n =
          (2 * (2 : ℝ) ^ n / n) * Real.log ((n : ℝ) / 2) + 2 * (2 : ℝ) ^ n / n := by ring
        _ ≤ (2 * (2 : ℝ) ^ n / n) * Real.log n + 2 * (2 : ℝ) ^ n / n :=
          add_le_add hmul le_rfl
        _ = (2 * Real.log n / (n : ℝ) + 2 / (n : ℝ)) * (2 : ℝ) ^ n := by ring

end HeadComplexity
