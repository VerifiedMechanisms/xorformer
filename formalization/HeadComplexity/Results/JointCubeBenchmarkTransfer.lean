import HeadComplexity.Results.LargeDomainWeightedTangent

set_option linter.style.header false

/-!
# Quantitative targets for a joint cube decoder

These are conditional transfers, not new decoder existence assertions.
They make the gain needed from a growing family explicit, including the
exceptional face and the two banks of a permutation tangent construction.
-/

namespace HeadComplexity.AxisZeroGluing

private theorem eighteen_mul_sq_le_two_pow {s : ℕ} (hs : 16 ≤ s) :
    18 * s ^ 2 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      calc
        18 * (s + 1) ^ 2 ≤ (18 * s ^ 2) * 2 := by nlinarith
        _ ≤ 2 ^ s * 2 := Nat.mul_le_mul_right 2 ih
        _ = 2 ^ (s + 1) := by rw [pow_succ]

/-- A decoder gain `g` survives the global cover at an absolute cost.
The exception face is absorbed explicitly, rather than dropped from the count. -/
theorem worstCaseHeadComplexity_real_le_of_cube_star_gain {k s M : ℕ}
    (hs : 16 ≤ s) (hbalance : k + s ≤ 3 * s)
    (g A : ℝ) (hg : 0 < g) (hgn : g ≤ k + s) (_hA : 0 ≤ A)
    (hbudget : (M : ℝ) * g ≤ A * (2 : ℝ) ^ k)
    (hcompiler : HasReverseCubeStarCompiler k s M) :
    (worstCaseHeadComplexity (k + s) : ℝ) ≤
      (66 * A + 1) * (2 : ℝ) ^ (k + s) / (((k + s : ℕ) : ℝ) * g) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hnpos : (0 : ℝ) < (k + s : ℕ) := by
    exact_mod_cast (show 0 < k + s by omega)
  have hnle : ((k + s : ℕ) : ℝ) ≤ 3 * (s : ℝ) := by exact_mod_cast hbalance
  have hpow : 18 * (s : ℝ) ^ 2 ≤ (2 : ℝ) ^ s := by
    exact_mod_cast eighteen_mul_sq_le_two_pow hs
  have hgn' : g ≤ ((k + s : ℕ) : ℝ) := by simpa only [Nat.cast_add] using hgn
  have hexception : (2 : ℝ) ^ (k + 1) * (((k + s : ℕ) : ℝ) * g) ≤
      (2 : ℝ) ^ (k + s) := by
    have hsmall : 2 * (((k + s : ℕ) : ℝ) * g) ≤ (2 : ℝ) ^ s := by
      have hprod := mul_le_mul_of_nonneg_left hgn' hnpos.le
      nlinarith
    rw [pow_succ, pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hsmall (show (0 : ℝ) ≤ 2 ^ k by positivity)]
  have hmain : (22 * (2 : ℝ) ^ s * M / s) *
      (((k + s : ℕ) : ℝ) * g) ≤ 66 * A * (2 : ℝ) ^ (k + s) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hspos).2
    rw [pow_add]
    have hb := mul_le_mul_of_nonneg_left hbudget
      (show (0 : ℝ) ≤ 66 * (2 : ℝ) ^ s * s by positivity)
    have hn := mul_le_mul_of_nonneg_left hnle
      (show (0 : ℝ) ≤ 22 * (2 : ℝ) ^ s * M * g by positivity)
    nlinarith
  have hglobal := worstCaseHeadComplexity_real_le_of_cube_star_compiler
    (show 0 < s by omega) hcompiler
  apply (le_div_iff₀ (mul_pos hnpos hg)).mpr
  calc
    _ ≤ (22 * (2 : ℝ) ^ s * M / s + 2 ^ (k + 1)) *
        (((k + s : ℕ) : ℝ) * g) :=
      mul_le_mul_of_nonneg_right hglobal (mul_pos hnpos hg).le
    _ = (22 * (2 : ℝ) ^ s * M / s) * (((k + s : ℕ) : ℝ) * g) +
        2 ^ (k + 1) * (((k + s : ℕ) : ℝ) * g) := by ring
    _ ≤ 66 * A * (2 : ℝ) ^ (k + s) + (2 : ℝ) ^ (k + s) :=
      add_le_add hmain hexception
    _ = _ := by ring

end HeadComplexity.AxisZeroGluing

namespace HeadComplexity.LargeDomain

open AxisZeroGluing

/-- Two tangent banks cost exactly a factor two in the decoder budget. -/
theorem worstCaseHeadComplexity_real_le_of_weighted_tangent_gain {k s H : ℕ}
    (hs : 16 ≤ s) (hbalance : k + s ≤ 3 * s)
    (g A : ℝ) (hg : 0 < g) (hgn : g ≤ k + s) (hA : 0 ≤ A)
    (hbudget : (H : ℝ) * g ≤ A * (2 : ℝ) ^ k)
    (hdecoder : HasCompactWeightedPermutationTangentDecoder k s H) :
    (worstCaseHeadComplexity (k + s) : ℝ) ≤
      (132 * A + 1) * (2 : ℝ) ^ (k + s) / (((k + s : ℕ) : ℝ) * g) := by
  have ht := worstCaseHeadComplexity_real_le_of_cube_star_gain hs hbalance g (2 * A)
    hg hgn (by positivity)
    (show ((H + H : ℕ) : ℝ) * g ≤ 2 * A * (2 : ℝ) ^ k by
      push_cast
      nlinarith)
    (hasReverseCubeStarCompiler_of_weightedPermutationTangent hdecoder)
  convert ht using 1
  ring

/-- A square-root compression of the cube rows would reach the requested
exponent one half in the original model. The existence hypothesis is explicit. -/
theorem worstCaseHeadComplexity_real_le_of_weighted_tangent_sqrt_gain {k s H : ℕ}
    (hs : 16 ≤ s) (hk : 1 ≤ k)
    (hbalance : k + s ≤ 3 * s) (hrow : k + s ≤ 4 * k)
    (A : ℝ) (hA : 0 ≤ A)
    (hbudget : (H : ℝ) * Real.sqrt k ≤ A * (2 : ℝ) ^ k)
    (hdecoder : HasCompactWeightedPermutationTangentDecoder k s H) :
    (worstCaseHeadComplexity (k + s) : ℝ) ≤
      (264 * A + 2) * (2 : ℝ) ^ (k + s) /
        (((k + s : ℕ) : ℝ) * Real.sqrt (k + s : ℕ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnpos : (0 : ℝ) < (k + s : ℕ) := by
    exact_mod_cast (show 0 < k + s by omega)
  have hsqrtpos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkpos
  have hnrootpos : 0 < Real.sqrt ((k + s : ℕ) : ℝ) := Real.sqrt_pos.2 hnpos
  have hrootle : Real.sqrt (k : ℝ) ≤ (k : ℝ) := by
    apply (Real.sqrt_le_left (by positivity)).2
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hgn : Real.sqrt (k : ℝ) ≤ (k : ℝ) + s := by
    nlinarith [show (0 : ℝ) ≤ s by positivity]
  have hrow' : ((k + s : ℕ) : ℝ) ≤ 4 * (k : ℝ) := by exact_mod_cast hrow
  have hroot : Real.sqrt ((k + s : ℕ) : ℝ) ≤ 2 * Real.sqrt (k : ℝ) := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [Real.sq_sqrt hkpos.le]
  have ht := worstCaseHeadComplexity_real_le_of_weighted_tangent_gain hs hbalance
    (Real.sqrt k) A hsqrtpos hgn hA hbudget hdecoder
  apply ht.trans
  apply (div_le_div_iff₀ (mul_pos hnpos hsqrtpos) (mul_pos hnpos hnrootpos)).2
  have hmult := mul_le_mul_of_nonneg_left hroot
    (show (0 : ℝ) ≤ (132 * A + 1) * (2 : ℝ) ^ (k + s) * ((k + s : ℕ) : ℝ) by positivity)
  nlinarith

/-- A balanced split gives the benchmark for every `n ≥ 32`, provided the
specified local decoder and square-root budget are supplied. -/
theorem worstCaseHeadComplexity_real_le_sqrt_of_balanced_weighted_tangent
    {n H : ℕ} (hn : 32 ≤ n) (A : ℝ) (hA : 0 ≤ A)
    (hbudget : (H : ℝ) * Real.sqrt (n / 2 : ℕ) ≤ A * (2 : ℝ) ^ (n / 2))
    (hdecoder : HasCompactWeightedPermutationTangentDecoder (n / 2) (n - n / 2) H) :
    (worstCaseHeadComplexity n : ℝ) ≤
      (264 * A + 2) * (2 : ℝ) ^ n / ((n : ℝ) * Real.sqrt n) := by
  have hsplit : n / 2 + (n - n / 2) = n := by omega
  have ht := worstCaseHeadComplexity_real_le_of_weighted_tangent_sqrt_gain
    (show 16 ≤ n - n / 2 by omega) (show 1 ≤ n / 2 by omega)
    (show n / 2 + (n - n / 2) ≤ 3 * (n - n / 2) by omega)
    (show n / 2 + (n - n / 2) ≤ 4 * (n / 2) by omega)
    A hA hbudget hdecoder
  simpa only [hsplit] using ht

end HeadComplexity.LargeDomain
