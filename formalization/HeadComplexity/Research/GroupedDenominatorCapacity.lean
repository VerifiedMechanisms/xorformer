import HeadComplexity.Research.LowParameterDenominatorCapacity

set_option linter.style.header false

/-!
Several independently chosen affine families of denominator slopes. The whole
score is cleared once, so arbitrary cancellation between groups is retained.
-/
noncomputable section
namespace HeadComplexity.GroupedDenominatorCapacity
open Finset MvPolynomial PolynomialRootCount
open scoped BigOperators
variable {n H G r : ℕ}

abbrev DenParameter (n H G r : ℕ) :=
  (Fin H × Fin r) ⊕ (Fin G × Fin (r + 1) × Fin n)

@[simp] theorem card_denParameter : Fintype.card (DenParameter n H G r) =
    r * H + n * (r + 1) * G := by simp [DenParameter]; ring

abbrev Parameter (n H G r : ℕ) :=
  LowParameterDenominatorCapacity.Parameter n H (Fintype.card (DenParameter n H G r))

def denVar (z : DenParameter n H G r) : MvPolynomial (Parameter n H G r) ℝ :=
  X (Sum.inr (Fintype.equivFin (DenParameter n H G r) z))

def statisticPoly (g : Fin G) (j : Fin (r + 1)) (x : Fin n → Bool) :
    MvPolynomial (Parameter n H G r) ℝ :=
  ∑ i, C (boolToReal (x i)) * denVar (Sum.inr (g, j, i))

def denPoly (group : Fin H → Fin G) (h : Fin H) (x : Fin n → Bool) :
    MvPolynomial (Parameter n H G r) ℝ :=
  1 + statisticPoly (group h) 0 x +
    ∑ j : Fin r, denVar (Sum.inl (h, j)) * statisticPoly (group h) j.succ x

theorem denVar_weighted (k : ℕ) (z : DenParameter n H G r) :
    WeightedDegreeLE (LowParameterDenominatorCapacity.parameterWeight k) (denVar z) 1 := by
  simpa [denVar, LowParameterDenominatorCapacity.parameterWeight] using
    weightedDegreeLE_X (R := ℝ)
      (LowParameterDenominatorCapacity.parameterWeight (n := n) (H := H)
        (q := Fintype.card (DenParameter n H G r)) k)
      (Sum.inr (Fintype.equivFin (DenParameter n H G r) z))

theorem statisticPoly_weighted (k : ℕ) (g : Fin G) (j : Fin (r + 1))
    (x : Fin n → Bool) :
    WeightedDegreeLE (LowParameterDenominatorCapacity.parameterWeight k)
      (statisticPoly (H := H) g j x) 1 := by
  apply weightedDegreeLE_sum
  intro i _
  exact weightedDegreeLE_C_mul _ (denVar_weighted k _)

theorem denPoly_weighted (k : ℕ) (group : Fin H → Fin G) (h : Fin H)
    (x : Fin n → Bool) :
    WeightedDegreeLE (LowParameterDenominatorCapacity.parameterWeight k)
      (denPoly (r := r) group h x) 2 := by
  apply weightedDegreeLE_add
  · apply weightedDegreeLE_add
    · simpa using weightedDegreeLE_mono
        (weightedDegreeLE_C (R := ℝ)
          (LowParameterDenominatorCapacity.parameterWeight k) 1) (show 0 ≤ 2 by omega)
    · exact weightedDegreeLE_mono (statisticPoly_weighted k _ _ _) (by omega)
  · apply weightedDegreeLE_sum
    intro j _
    simpa using weightedDegreeLE_mul (denVar_weighted k (Sum.inl (h, j)))
      (statisticPoly_weighted k (group h) j.succ x)

def represented (n H G r : ℕ) : Set ((Fin n → Bool) → Bool) :=
  ⋃ group : Fin H → Fin G,
    LowParameterDenominatorCapacity.represented (denPoly (n := n) (r := r) group)

def denPoint (v : Fin H → Fin r → ℝ) (u : Fin G → Fin (r + 1) → Fin n → ℝ) :
    DenParameter n H G r → ℝ
  | Sum.inl (h, j) => v h j
  | Sum.inr (g, j, i) => u g j i

def parameterPoint (a : Fin H → Fin n → ℝ) (v : Fin H → Fin r → ℝ)
    (u : Fin G → Fin (r + 1) → Fin n → ℝ) : Parameter n H G r → ℝ
  | Sum.inl (h, i) => a h i
  | Sum.inr z => denPoint v u ((Fintype.equivFin (DenParameter n H G r)).symm z)

def normalizedPoint (group : Fin H → Fin G) (a : Fin H → Fin n → ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin G → Fin (r + 1) → Fin n → ℝ) :
    NormalizedCounting.Parameter n H → ℝ
  | (h, false, i) => a h i
  | (h, true, i) => u (group h) 0 i + ∑ j, v h j * u (group h) j.succ i

theorem eval_denVar (a : Fin H → Fin n → ℝ) (v : Fin H → Fin r → ℝ)
    (u : Fin G → Fin (r + 1) → Fin n → ℝ) (z : DenParameter n H G r) :
    eval (parameterPoint a v u) (denVar z) = denPoint v u z := by
  simp [denVar, parameterPoint]

theorem eval_numPoly (group : Fin H → Fin G) (a : Fin H → Fin n → ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin G → Fin (r + 1) → Fin n → ℝ)
    (h : Fin H) (x : Fin n → Bool) :
    eval (parameterPoint a v u) (LowParameterDenominatorCapacity.numPoly h x) =
      eval (normalizedPoint group a v u) (NormalizedCounting.linearPoly false h x) := by
  simp [LowParameterDenominatorCapacity.numPoly, NormalizedCounting.linearPoly,
    parameterPoint, normalizedPoint]

theorem eval_denPoly (group : Fin H → Fin G) (a : Fin H → Fin n → ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin G → Fin (r + 1) → Fin n → ℝ)
    (h : Fin H) (x : Fin n → Bool) :
    eval (parameterPoint a v u) (denPoly group h x) =
      eval (normalizedPoint group a v u) (NormalizedCounting.denPoly h x) := by
  simp only [denPoly, statisticPoly, NormalizedCounting.denPoly,
    NormalizedCounting.linearPoly, map_add, map_one, map_sum, map_mul,
    eval_X, eval_C, eval_denVar, denPoint, normalizedPoint, Finset.mul_sum,
    Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_comm (f := fun j i ↦ v h j * (boolToReal (x i) * u (group h) j.succ i))]
  simp_rw [mul_left_comm (v h _) (boolToReal _)]; ring

theorem eval_clearedPoly (group : Fin H → Fin G) (a : Fin H → Fin n → ℝ)
    (v : Fin H → Fin r → ℝ) (u : Fin G → Fin (r + 1) → Fin n → ℝ)
    (s : Bool) (x : Fin n → Bool) :
    eval (parameterPoint a v u) (LowParameterDenominatorCapacity.clearedPoly (denPoly group) s x) =
      eval (normalizedPoint group a v u) (NormalizedCounting.clearedPoly s x) := by
  simp only [LowParameterDenominatorCapacity.clearedPoly, NormalizedCounting.clearedPoly,
    map_add, map_mul, map_prod, map_sum, eval_C, eval_numPoly group, eval_denPoly]

theorem mem_represented_of_normalized (θ : NormalizedCounting.Parameter n H → ℝ)
    (group : Fin H → Fin G) (v : Fin H → Fin r → ℝ)
    (u : Fin G → Fin (r + 1) → Fin n → ℝ)
    (hfactor : ∀ h i, θ (h, true, i) =
      u (group h) 0 i + ∑ j, v h j * u (group h) j.succ i)
    (s : Bool) (f : (Fin n → Bool) → Bool)
    (hstrict : ∀ x, if f x then 0 < eval θ (NormalizedCounting.clearedPoly s x)
      else eval θ (NormalizedCounting.clearedPoly s x) < 0) :
    f ∈ represented n H G r := by
  let a : Fin H → Fin n → ℝ := fun h i ↦ θ (h, false, i)
  have hpoint : normalizedPoint group a v u = θ := by
    funext z
    rcases z with ⟨h, kind, i⟩
    cases kind
    · rfl
    · exact (hfactor h i).symm
  apply Set.mem_iUnion.mpr
  refine ⟨group, ?_⟩
  have hm : f ∈ strictPolynomialSignPatterns
      (LowParameterDenominatorCapacity.clearedPoly (denPoly (r := r) group) s) := by
    refine ⟨parameterPoint a v u, fun x ↦ ?_⟩
    rw [eval_clearedPoly, hpoint]
    exact hstrict x
  cases s
  · exact Or.inl hm
  · exact Or.inr hm

theorem mem_represented_of_affine (A : AffineFractionFamily n H) (c : ℝ)
    (group : Fin H → Fin G) (v : Fin H → Fin r → ℝ)
    (u : Fin G → Fin (r + 1) → Fin n → ℝ)
    (hfactor : ∀ h i, (A.den h).coeff (Finsupp.single i 1) / (A.den h).coeff 0 =
      u (group h) 0 i + ∑ j, v h j * u (group h) j.succ i)
    (f : (Fin n → Bool) → Bool)
    (hstrict : ∀ x, if f x then
      0 < c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h)
      else c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h) < 0) :
    f ∈ represented n H G r := by
  classical
  let t : ℝ := c + ∑ h, (A.num h).coeff 0 / (A.den h).coeff 0
  have hzero := hstrict (fun _ ↦ false)
  simp only [NormalizedCounting.eval_affine_zero _ (A.num_degree _),
    NormalizedCounting.eval_affine_zero _ (A.den_degree _)] at hzero
  have htne : t ≠ 0 := by
    cases hval : f (fun _ ↦ false) <;> simp only [hval, Bool.false_eq_true,
      ↓reduceIte] at hzero
    · exact ne_of_lt hzero
    · exact ne_of_gt hzero
  have ht : 0 < |t| := abs_pos.mpr htne
  have hsign : (if f (fun _ ↦ false) then (1 : ℝ) else -1) = t / |t| := by
    cases hval : f (fun _ ↦ false) <;> simp only [hval, Bool.false_eq_true,
      ↓reduceIte] at hzero ⊢
    · rw [abs_of_neg (show t < 0 from hzero)]
      field_simp
    · rw [abs_of_pos (show 0 < t from hzero), div_self htne]
  have hscore (x : Fin n → Bool) :
      NormalizedCounting.score (NormalizedCounting.parameterPoint A |t|)
        (f (fun _ ↦ false)) x =
        (c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h)) / |t| := by
    unfold NormalizedCounting.score
    rw [hsign]
    simp_rw [NormalizedCounting.normalized_head_eval A ht.ne']
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    dsimp [t]
    ring
  apply mem_represented_of_normalized (NormalizedCounting.parameterPoint A |t|)
    group v u hfactor (f (fun _ ↦ false)) f
  intro x
  rw [NormalizedCounting.eval_clearedPoly _ _ _
    (fun h ↦ (NormalizedCounting.eval_denPoly_pos A |t| h x).ne'), hscore]
  have hp : 0 < ∏ h : Fin H, eval (NormalizedCounting.parameterPoint A |t|)
      (NormalizedCounting.denPoly h x) :=
    Finset.prod_pos (fun h _ ↦ NormalizedCounting.eval_denPoly_pos A |t| h x)
  have hx := hstrict x
  cases hfx : f x <;> simp only [hfx, Bool.false_eq_true, ↓reduceIte] at hx ⊢
  · exact mul_neg_of_pos_of_neg hp (div_neg_of_neg_of_pos hx ht)
  · exact mul_pos hp (div_pos hx ht)

/-- Original admissible atoms are included whenever their normalized slopes
factor through the indicated shared statistics. The atoms are not replaced. -/
theorem mem_represented_of_original (φ : Fin H → FracAtom n) (c : ℝ)
    (group : Fin H → Fin G) (v : Fin H → Fin r → ℝ)
    (u : Fin G → Fin (r + 1) → Fin n → ℝ)
    (hfactor : ∀ h i, ((FracAtom.affineFamily φ).den h).coeff (Finsupp.single i 1) /
      ((FracAtom.affineFamily φ).den h).coeff 0 = u (group h) 0 i + ∑ j, v h j * u (group h) j.succ i)
    (f : (Fin n → Bool) → Bool)
    (hstrict : ∀ x, if f x then 0 < c + ∑ h, (φ h).eval x
      else c + ∑ h, (φ h).eval x < 0) :
    f ∈ represented n H G r := by
  apply mem_represented_of_affine (FracAtom.affineFamily φ) c group v u hfactor f
  intro x
  simpa only [FracAtom.affineFamily, ← FracAtom.eval_eq_numPoly_div_denPoly] using hstrict x


/-- Target-dependent assignments of heads to groups are included in this
count. There is no assumption about the signs of different group scores. -/
theorem card_represented_le_exp {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hq : (r : ℝ) * H + n * (r + 1) * G ≤ 2 * t * H)
    (hH : 0 < H) (hG : G ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (400 * n * t)) :
    ((represented n H G r).ncard : ℝ) ≤ Real.exp (8 * (2 : ℝ) ^ n / 25) := by
  apply LowParameterDenominatorCapacity.card_chart_union_le_exp _ hn htlo hthi
    (by simpa only [card_denParameter, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hq)
    hH (fun group h x ↦ denPoly_weighted (2 * H) group h x) hwidth
  simp only [Fintype.card_fun, Fintype.card_fin]
  by_cases hG0 : G = 0
  · simp [hG0, Nat.ne_of_gt hH, (Real.exp_pos _).le]
  have hGpos : (0 : ℝ) < G := by exact_mod_cast (Nat.pos_of_ne_zero hG0)
  have hGn : (G : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hG
  have hl := Real.log_le_log hGpos hGn
  rw [Real.log_pow] at hl
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogG : Real.log (G : ℝ) ≤ n :=
    hl.trans (by nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
  have hnR : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : 1 ≤ t := by
    apply le_trans _ htlo
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hbudget := (le_div_iff₀ (by positivity : 0 < 400 * (n : ℝ) * t)).mp hwidth
  have hbound : (H : ℝ) * Real.log G ≤ (2 : ℝ) ^ n / 50 := by
    have hm := mul_le_mul_of_nonneg_left hlogG (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
    have htH := mul_le_mul_of_nonneg_left ht1 (show 0 ≤ (n : ℝ) * H by positivity)
    nlinarith
  push_cast
  rw [← Real.exp_log hGpos, ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr hbound

theorem card_represented_le_half_tables {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hq : (r : ℝ) * H + n * (r + 1) * G ≤ 2 * t * H)
    (hH : 0 < H) (hG : G ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (400 * n * t)) :
    (represented n H G r).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  have hc := card_represented_le_exp hn htlo hthi hq hH hG hwidth
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have hlog : (16 : ℝ) / 25 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexp : 8 * (2 : ℝ) ^ n / 25 ≤ ((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2 := by
    rw [hpow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hlog (show 0 ≤ (2 : ℝ) ^ (n - 1) by positivity)]
  have hreal : ((represented n H G r).ncard : ℝ) ≤ (2 : ℝ) ^ (2 ^ (n - 1)) := by
    calc
      _ ≤ _ := hc
      _ ≤ Real.exp (((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast hreal

theorem card_represented_sqrt_scale (hn : 32 ≤ n)
    (hq : (r : ℝ) * H + n * (r + 1) * G ≤ 2 * Real.sqrt n * H)
    (hH : 0 < H) (hG : G ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (400 * n * Real.sqrt n)) :
    (represented n H G r).ncard ≤ 2 ^ (2 ^ (n - 1)) :=
  card_represented_le_half_tables hn (MarginCapacityEstimates.sqrt_test_range hn).1
    (MarginCapacityEstimates.sqrt_test_range hn).2 hq hH hG hwidth

theorem card_represented_logarithmic_scale (hn : 32 ≤ n)
    (hq : (r : ℝ) * H + n * (r + 1) * G ≤ 2 * ((n : ℝ) / Real.log n) * H)
    (hH : 0 < H) (hG : G ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n * Real.log n / (400 * (n : ℝ) ^ 2)) :
    (represented n H G r).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  apply card_represented_le_half_tables hn
    (MarginCapacityEstimates.logarithmic_test_range hn).1
    (MarginCapacityEstimates.logarithmic_test_range hn).2 hq hH hG
  convert hwidth using 1
  field_simp

theorem worstCase_gt_of_grouped_or_margin {K : ℕ} {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hq : (r : ℝ) * K + n * (r + 1) * G ≤ 2 * t * K)
    (hK : 0 < K) (hG : G ≤ 2 ^ n)
    (hwidth : (K : ℝ) ≤ (2 : ℝ) ^ n / (400 * n * t))
    (hcover : headComputableFunctions n H ⊆
      RelativeMarginQuantifiers.highMarginFunctions n K (MarginCapacityEstimates.testMargin t) ∪
        represented n K G r) : H < worstCaseHeadComplexity n := by
  have hnR : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : 1 ≤ t := by
    apply le_trans _ htlo
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hwidth' : (K : ℝ) ≤ (2 : ℝ) ^ n / (100 * n * t) := hwidth.trans (by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith)
  have hhigh := MarginCapacityEstimates.card_highMargin_test_at_width hn htlo hthi hwidth'
  have hlow := card_represented_le_half_tables hn htlo hthi hq hK hG hwidth
  have hc : (headComputableFunctions n H).ncard ≤ 2 * 2 ^ (2 ^ (n - 1)) := by
    calc
      _ ≤ _ := Set.ncard_le_ncard hcover
      _ ≤ _ := Set.ncard_union_le _ _
      _ ≤ 2 ^ (2 ^ (n - 1)) + 2 ^ (2 ^ (n - 1)) := Nat.add_le_add hhigh hlow
      _ = _ := by omega
  have hpower : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    omega
  have hNhalf : 1 < (2 : ℕ) ^ (n - 1) := one_lt_pow₀ (by norm_num) (by omega)
  have hstrict : 2 * (2 : ℕ) ^ (2 ^ (n - 1)) < 2 ^ (2 ^ n) := by
    rw [show 2 * (2 : ℕ) ^ (2 ^ (n - 1)) = 2 ^ (2 ^ (n - 1) + 1) by
      rw [pow_succ]; omega]
    apply Nat.pow_lt_pow_right (by norm_num)
    omega
  obtain ⟨f, hf⟩ := exists_HStar_gt_of_card_lt (hc.trans_lt hstrict)
  exact hf.trans_le (HStar_le_worstCaseHeadComplexity f)

/-- Equivalent exceptional-table formulation: the premise quantifies over
targets for which every comparison-width representation has small margin. -/
theorem worstCase_gt_of_low_margin_grouped_statistics {K : ℕ} {t : ℝ}
    (hn : 32 ≤ n) (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hq : (r : ℝ) * K + n * (r + 1) * G ≤ 2 * t * K)
    (hK : 0 < K) (hG : G ≤ 2 ^ n)
    (hwidth : (K : ℝ) ≤ (2 : ℝ) ^ n / (400 * n * t))
    (hlow : RelativeMarginQuantifiers.allRepresentationsLowMargin n H K
      (MarginCapacityEstimates.testMargin t) ⊆ represented n K G r) :
    H < worstCaseHeadComplexity n := by
  apply worstCase_gt_of_grouped_or_margin hn htlo hthi hq hK hG hwidth
  intro f hf
  by_cases hg : f ∈ RelativeMarginQuantifiers.highMarginFunctions n K
      (MarginCapacityEstimates.testMargin t)
  · exact Or.inl hg
  · exact Or.inr (hlow ⟨hf, hg⟩)


end HeadComplexity.GroupedDenominatorCapacity
