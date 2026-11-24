import HeadComplexity.Research.NormalizedLogCounting
import HeadComplexity.Polynomial.WeightedPolynomialSignCount

set_option linter.style.header false

/-!
Weighted unrestricted counting after exact zero-input normalization. Numerator
variables occur linearly, so assigning them a large weight retains a factor
`k ^ (n * H)` in the Warren denominator. No model or margin restriction is imposed.
-/

noncomputable section
namespace HeadComplexity.WeightedNormalizedCounting
open Finset MvPolynomial PolynomialRootCount NormalizedCounting
open scoped BigOperators

variable {n H : ℕ}

def parameterWeight (k : ℕ) : Parameter n H → ℕ
  | (_, kind, _) => if kind then 1 else k

theorem linearPoly_weighted (k : ℕ) (kind : Bool) (h : Fin H) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (linearPoly kind h x) (if kind then 1 else k) := by
  apply weightedDegreeLE_sum
  intro i _
  apply weightedDegreeLE_C_mul
  simpa [parameterWeight] using
    (weightedDegreeLE_X (R := ℝ) (parameterWeight (n := n) (H := H) k) (h, kind, i))

theorem denPoly_weighted (k : ℕ) (h : Fin H) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (denPoly h x) 1 := by
  apply weightedDegreeLE_add
  · simpa using weightedDegreeLE_mono
      (weightedDegreeLE_C (R := ℝ) (parameterWeight k) 1) (show 0 ≤ 1 by omega)
  · simpa using linearPoly_weighted k true h x

theorem denProd_weighted (k : ℕ) (I : Finset (Fin H)) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (∏ h ∈ I, denPoly h x) I.card := by
  simpa using weightedDegreeLE_prod I (D := fun _ ↦ 1)
    (fun h _ ↦ denPoly_weighted k h x)

theorem clearedPoly_weighted (k : ℕ) (hk : 0 < k) (hH : 0 < H)
    (s : Bool) (x : Fin n → Bool) :
    WeightedDegreeLE (parameterWeight k) (clearedPoly (H := H) s x) (H + k - 1) := by
  classical
  apply weightedDegreeLE_add
  · apply weightedDegreeLE_mono
      (weightedDegreeLE_C_mul _ (denProd_weighted k Finset.univ x))
    simp only [Finset.card_fin]
    omega
  · apply weightedDegreeLE_sum
    intro h _
    have hd := denProd_weighted k (Finset.univ.erase h) x
    rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_fin] at hd
    have hl : WeightedDegreeLE (parameterWeight k) (linearPoly false h x) k := by
      simpa using linearPoly_weighted k false h x
    exact weightedDegreeLE_mono (weightedDegreeLE_mul hl hd) (by omega)

theorem product_parameter_weights (k : ℕ) :
    (∏ i : Parameter n H, (parameterWeight k i : ℝ)) = (k : ℝ) ^ (n * H) := by
  classical
  simp only [Fintype.prod_prod_type, parameterWeight, Fintype.prod_bool,
    Bool.false_eq_true, ↓reduceIte, Nat.cast_one, Finset.prod_const_one,
    Finset.prod_const, Finset.card_fin, one_mul]
  rw [← pow_mul]

/-- A one-parameter family of exact weighted counts. -/
theorem card_le_weighted (k : ℕ) (hk : 0 < k)
    (hn : 0 < n) (hH : 0 < H) (hp : 2 * n * H ≤ 2 ^ n) :
    ((headComputableFunctions n H).ncard : ℝ) ≤
      2 * (4 * Real.exp 1 * (H + k - 1 : ℕ) * (2 : ℝ) ^ n /
        (2 * n * H)) ^ (2 * n * H) / (k : ℝ) ^ (n * H) := by
  have hc (s : Bool) := weightedStrictPolynomialSignPatterns_card_le
    (K := Parameter n H) (by rw [card_parameter]; positivity)
    (by rw [card_parameter]
        simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hp)
    (parameterWeight k)
    (fun i ↦ by rcases i with ⟨h, kind, i⟩; cases kind <;> simp [parameterWeight, hk])
    (fun i ↦ by rcases i with ⟨h, kind, i⟩; cases kind <;>
      simp [parameterWeight] <;> omega)
    (clearedPoly (H := H) s) (clearedPoly_weighted k hk hH s)
  have hb (s : Bool) :
      ((strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) s)).ncard : ℝ) ≤
        (4 * Real.exp 1 * (H + k - 1 : ℕ) * (2 : ℝ) ^ n /
          (2 * n * H)) ^ (2 * n * H) / (k : ℝ) ^ (n * H) := by
    simpa only [card_parameter, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, product_parameter_weights, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_pow] using hc s
  have ht : ((headComputableFunctions n H).ncard : ℝ) ≤
      ((strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) false)).ncard : ℝ) +
      ((strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) true)).ncard : ℝ) := by
    exact_mod_cast (card_le_two_patterns (n := n) (H := H))
  have := add_le_add (hb false) (hb true)
  calc
    _ ≤ _ := ht.trans this
    _ = _ := by ring

/-- A convenient simplified weighted bound, saving half the old leading
entropy exponent at widths of order `2 ^ n / n ^ 2`. -/
theorem card_le (hn : 0 < n) (hH : 0 < H) (hp : 2 * n * H ≤ 2 ^ n) :
    ((headComputableFunctions n H).ncard : ℝ) ≤
      2 * (16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 /
        ((n : ℝ) ^ 2 * H)) ^ (n * H) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have heR : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
  have hD : ((H + H - 1 : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by
    exact_mod_cast (show H + H - 1 ≤ 2 * H by omega)
  have hc := card_le_weighted H hH hn hH hp
  have hraw : ((headComputableFunctions n H).ncard : ℝ) ≤
      2 * (4 * Real.exp 1 * (2 * (H : ℝ)) * (2 : ℝ) ^ n /
        (2 * n * H)) ^ (2 * n * H) / (H : ℝ) ^ (n * H) := by
    refine hc.trans ?_
    gcongr
  have hb : 4 * Real.exp 1 * (2 * (H : ℝ)) * (2 : ℝ) ^ n /
      (2 * n * H) = 4 * Real.exp 1 * (2 : ℝ) ^ n / n := by
    field_simp
  rw [hb] at hraw
  have hexp : 2 * n * H = 2 * (n * H) := by ring
  rw [hexp, pow_mul] at hraw
  have hid : 2 * ((4 * Real.exp 1 * (2 : ℝ) ^ n / n) ^ 2) ^ (n * H) /
      (H : ℝ) ^ (n * H) =
      2 * (16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 /
        ((n : ℝ) ^ 2 * H)) ^ (n * H) := by
    rw [mul_div_assoc, ← div_pow]
    congr 2
    field_simp
    ring
  rwa [hid] at hraw

/-- The optimal uniform numerator weight is `H - 1` for `H≥2`. -/
theorem card_le_optimal (hn : 0 < n) (hH : 2 ≤ H) (hp : 2 * n * H ≤ 2 ^ n) :
    ((headComputableFunctions n H).ncard : ℝ) ≤
      2 * (16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 * ((H - 1 : ℕ) : ℝ) /
        ((n : ℝ) ^ 2 * (H : ℝ) ^ 2)) ^ (n * H) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hk : 0 < H - 1 := by omega
  have hkR : (0 : ℝ) < ((H - 1 : ℕ) : ℝ) := by exact_mod_cast hk
  have hc := card_le_weighted (H - 1) hk hn (by omega) hp
  have hD : H + (H - 1)-1 = 2 * (H - 1) := by omega
  rw [hD, Nat.cast_mul, Nat.cast_ofNat] at hc
  have hexp : 2 * n * H = 2 * (n * H) := by ring
  have hid : 2 * (4 * Real.exp 1 * (2 * ((H - 1 : ℕ) : ℝ)) * (2 : ℝ) ^ n /
      (2 * n * H)) ^ (2 * n * H) / (((H - 1 : ℕ) : ℝ) ^ (n * H)) =
      2 * (16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 * ((H - 1 : ℕ) : ℝ) /
        ((n : ℝ) ^ 2 * (H : ℝ) ^ 2)) ^ (n * H) := by
    rw [hexp, pow_mul, mul_div_assoc, ← div_pow]
    congr 2
    field_simp
    ring
  rwa [hid] at hc

/-- Any upper bound for the weighted base gives an entropy inequality at the
original worst-case width, including the case outside Warren's dimension range. -/
theorem entropy_at_worstCase_of_base (hn : 8 ≤ n) (B : ℝ) (hB : 4 ≤ B)
    (hbase : 16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 /
      ((n : ℝ) ^ 2 * (worstCaseHeadComplexity n : ℝ)) ≤ B) :
    ((2 : ℝ) ^ n - 1) * Real.log 2 ≤
      (n : ℝ) * (worstCaseHeadComplexity n : ℝ) * Real.log B := by
  have hnpos : 0 < n := by omega
  have hW : 0 < worstCaseHeadComplexity n :=
    (Nat.zero_le _).trans_lt (NormalizedCounting.worstCase_gt_div_all_large hn)
  have hBp : 0 < B := by linarith
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlB : 2 * Real.log 2 ≤ Real.log B := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hB
    have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rwa [hfour] at hh
  by_cases hp : 2 * n * worstCaseHeadComplexity n ≤ 2 ^ n
  · have hc := card_le hnpos hW hp
    have hc' : ((headComputableFunctions n (worstCaseHeadComplexity n)).ncard : ℝ) ≤
        2 * B ^ (n * worstCaseHeadComplexity n) := hc.trans (by gcongr)
    rw [NormalizedLogCounting.card_at_worstCase] at hc'
    have hh : (2 : ℝ) ^ (2 ^ n) ≤ 2 * B ^ (n * worstCaseHeadComplexity n) := by
      exact_mod_cast hc'
    have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ (2 ^ n)) hh
    rw [Real.log_mul (by norm_num) (pow_pos hBp _).ne', Real.log_pow,
      Real.log_pow] at hl
    push_cast at hl
    nlinarith
  · have hdim : (2 : ℝ) ^ n ≤ 2 * (n : ℝ) * (worstCaseHeadComplexity n : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hp))
    have hmul := mul_le_mul_of_nonneg_left hlB
      (show 0 ≤ (n : ℝ) * (worstCaseHeadComplexity n : ℝ) by positivity)
    have hdimlog := mul_le_mul_of_nonneg_right hdim hl2.le
    nlinarith

def entropyBase (n : ℕ) : ℝ :=
  32 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 / ((2 : ℝ) ^ n - 1)

theorem weighted_base_le_entropyBase (hn : 8 ≤ n) :
    16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 /
      ((n : ℝ) ^ 2 * (worstCaseHeadComplexity n : ℝ)) ≤ entropyBase n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : (1 : ℝ) < (2 : ℝ) ^ n := one_lt_pow₀ (by norm_num) (by omega)
  have hw := NormalizedCounting.worstCase_real_lower hn
  have hmul := (div_le_iff₀ (show 0 < 2 * (n : ℝ) * n by positivity)).mp hw
  have hd : ((2 : ℝ) ^ n - 1) / 2 ≤ (n : ℝ) ^ 2 * (worstCaseHeadComplexity n : ℝ) := by
    nlinarith
  have hh := div_le_div_of_nonneg_left
    (show 0 ≤ 16 * (Real.exp 1) ^ 2 * ((2 : ℝ) ^ n) ^ 2 by positivity)
    (show 0 < ((2 : ℝ) ^ n - 1) / 2 by positivity) hd
  calc
    _ ≤ _ := hh
    _ = entropyBase n := by unfold entropyBase; field_simp; ring

theorem entropyBase_ge_four (hn : 8 ≤ n) : 4 ≤ entropyBase n := by
  have hN : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
      (show 1 ≤ n by omega))
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have he2 : (1 : ℝ) ≤ (Real.exp 1) ^ 2 := by nlinarith [sq_nonneg (Real.exp 1 - 1)]
  unfold entropyBase
  apply (le_div_iff₀ (by linarith : 0 < (2 : ℝ) ^ n - 1)).mpr
  have hh := mul_le_mul_of_nonneg_right he2 (show 0 ≤ ((2 : ℝ) ^ n) ^ 2 by positivity)
  nlinarith [sq_nonneg ((2 : ℝ) ^ n - 1)]

theorem entropy_at_worstCase (hn : 8 ≤ n) :
    ((2 : ℝ) ^ n - 1) * Real.log 2 ≤
      (n : ℝ) * (worstCaseHeadComplexity n : ℝ) * Real.log (entropyBase n) :=
  entropy_at_worstCase_of_base hn _ (entropyBase_ge_four hn)
    (weighted_base_le_entropyBase hn)

/-- An unconditional finite logarithmic lower bound with asymptotic leading
constant one in front of `2 ^ n / n ^ 2`. -/
theorem worstCase_real_log_lower (hn : 8 ≤ n) :
    (((2 : ℝ) ^ n - 1) * Real.log 2) / ((n : ℝ) * Real.log (entropyBase n)) ≤
      (worstCaseHeadComplexity n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (entropyBase n) := Real.log_pos (by
    have := entropyBase_ge_four hn; linarith)
  apply (div_le_iff₀ (mul_pos hnR hlog)).mpr
  have hh := entropy_at_worstCase hn
  nlinarith

theorem entropyBase_le_two_pow (hn : 8 ≤ n) : entropyBase n ≤ (2 : ℝ) ^ (n + 8) := by
  have hN : (256 : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hn)
  have he : Real.exp (1 : ℝ) ≤ 11 / 4 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hep : 0 ≤ Real.exp (1 : ℝ) := (Real.exp_pos _).le
  have he2 : (Real.exp 1) ^ 2 ≤ 121 / 16 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right he2 (show 0 ≤ ((2 : ℝ) ^ n) ^ 2 by positivity)
  rw [pow_add]
  norm_num
  unfold entropyBase
  apply (div_le_iff₀ (by linarith : 0 < (2 : ℝ) ^ n - 1)).mpr
  nlinarith [sq_nonneg ((2 : ℝ) ^ n - 256)]

/-- A simple unconditional bound against the original worst-case definition.
This improves the leading constant but does not cross the `N / n ^ 2` barrier. -/
theorem worstCase_real_lower (hn : 8 ≤ n) :
    ((2 : ℝ) ^ n - 1) / ((n : ℝ) * (n + 8)) ≤ (worstCaseHeadComplexity n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbasepos : 0 < entropyBase n := by have := entropyBase_ge_four hn; linarith
  have hl := Real.log_le_log hbasepos (entropyBase_le_two_pow hn)
  rw [Real.log_pow] at hl
  push_cast at hl
  have hw := entropy_at_worstCase hn
  have hh := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ (n : ℝ) * (worstCaseHeadComplexity n : ℝ) by positivity)
  have hcancel : (2 : ℝ) ^ n - 1 ≤ (n : ℝ) * (n + 8) * (worstCaseHeadComplexity n : ℝ) := by
    nlinarith
  apply (div_le_iff₀ (show 0 < (n : ℝ) * (n + 8) by positivity)).mpr
  nlinarith

end HeadComplexity.WeightedNormalizedCounting
