import HeadComplexity.Results.WarrenBound

set_option linter.style.header false

/-!
# Exact normalization for unrestricted sign counting

Every strict score can be normalized at the zero input. Its bias then belongs
to `{−1,1}`, every denominator constant is one, and every numerator constant
is zero. This gives degree `H` predicates in precisely `2*n*H` parameters.
No amplitude, margin, coefficient-height, or cancellation restriction is used.
-/

namespace HeadComplexity.NormalizedCounting

open Finset MvPolynomial
open scoped BigOperators

variable {n H : ℕ}

abbrev Parameter (n H : ℕ) := Fin H × Bool × Fin n

@[simp] theorem card_parameter : Fintype.card (Parameter n H) = 2 * n * H := by
  simp [Parameter]
  ring

noncomputable def linearPoly (kind : Bool) (h : Fin H) (x : Fin n → Bool) :
    MvPolynomial (Parameter n H) ℝ :=
  ∑ i, C (boolToReal (x i)) * X (h, kind, i)

noncomputable def denPoly (h : Fin H) (x : Fin n → Bool) :
    MvPolynomial (Parameter n H) ℝ := 1 + linearPoly true h x

noncomputable def clearedPoly (s : Bool) (x : Fin n → Bool) :
    MvPolynomial (Parameter n H) ℝ :=
  C (if s then 1 else -1) * ∏ h, denPoly h x +
    ∑ h, linearPoly false h x * ∏ g ∈ Finset.univ.erase h, denPoly g x

theorem linearPoly_totalDegree_le (kind : Bool) (h : Fin H) (x : Fin n → Bool) :
    (linearPoly kind h x).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  refine (totalDegree_mul _ _).trans ?_
  simp

theorem denPoly_totalDegree_le (h : Fin H) (x : Fin n → Bool) :
    (denPoly h x).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le ?_ (linearPoly_totalDegree_le _ _ _))
  simp

private theorem prod_degree {ι K : Type*} (s : Finset ι)
    (P : ι → MvPolynomial K ℝ) (hP : ∀ i, (P i).totalDegree ≤ 1) :
    (∏ i ∈ s, P i).totalDegree ≤ s.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 (fun i _ ↦ hP i)).trans ?_
  simp

theorem clearedPoly_totalDegree_le (s : Bool) (x : Fin n → Bool) :
    (clearedPoly (H := H) s x).totalDegree ≤ H := by
  classical
  unfold clearedPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    simpa using prod_degree Finset.univ
      (fun h : Fin H ↦ denPoly h x) (fun h ↦ denPoly_totalDegree_le h x)
  · apply totalDegree_finsetSum_le
    intro h _
    refine (totalDegree_mul _ _).trans ?_
    have hp : (∏ g ∈ Finset.univ.erase h, denPoly g x).totalDegree ≤ H - 1 := by
      refine (prod_degree (Finset.univ.erase h)
        (fun g : Fin H ↦ denPoly g x) (fun g ↦ denPoly_totalDegree_le g x)).trans ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_fin]
    have hl := linearPoly_totalDegree_le false h x
    have hh : 0 < H := Nat.zero_lt_of_lt h.isLt
    omega

/-- The elementary field identity behind the normalization. -/
theorem normalized_fraction (a₀ b₀ u v t : ℝ) (hb : b₀ ≠ 0)
    (hd : b₀ + v ≠ 0) (ht : t ≠ 0) :
    ((u - a₀ / b₀ * v) / (b₀ * t)) / (1 + v / b₀) =
      ((a₀ + u) / (b₀ + v) - a₀ / b₀) / t := by
  have hd' : 1 + v / b₀ ≠ 0 := by
    rw [← div_self hb, ← add_div]
    exact div_ne_zero hd hb
  field_simp
  ring

noncomputable def slopeValue (P : MvPolynomial (Fin n) ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i, boolToReal (x i) * P.coeff (Finsupp.single i 1)

theorem eval_affine (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ 1)
    (x : Fin n → Bool) : eval (cubePoint x) P = P.coeff 0 + slopeValue P x := by
  simpa [slopeValue, mul_comm] using eval_cubePoint_affine P hP x

theorem eval_affine_zero (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ 1) :
    eval (cubePoint (fun _ : Fin n ↦ false)) P = P.coeff 0 := by
  rw [eval_affine P hP]
  simp [slopeValue, boolToReal]

noncomputable def parameterPoint (A : AffineFractionFamily n H) (t : ℝ) :
    Parameter n H → ℝ
  | (h, false, i) =>
      ((A.num h).coeff (Finsupp.single i 1) -
        ((A.num h).coeff 0 / (A.den h).coeff 0) *
          (A.den h).coeff (Finsupp.single i 1)) / ((A.den h).coeff 0 * t)
  | (h, true, i) => (A.den h).coeff (Finsupp.single i 1) / (A.den h).coeff 0

theorem eval_linear_false (A : AffineFractionFamily n H) (t : ℝ)
    (h : Fin H) (x : Fin n → Bool) :
    eval (parameterPoint A t) (linearPoly false h x) =
      (slopeValue (A.num h) x - ((A.num h).coeff 0 / (A.den h).coeff 0) *
        slopeValue (A.den h) x) / ((A.den h).coeff 0 * t) := by
  simp only [linearPoly, map_sum, map_mul, eval_C, eval_X, parameterPoint]
  simp only [slopeValue, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eval_linear_true (A : AffineFractionFamily n H) (t : ℝ)
    (h : Fin H) (x : Fin n → Bool) :
    eval (parameterPoint A t) (linearPoly true h x) =
      slopeValue (A.den h) x / (A.den h).coeff 0 := by
  simp [linearPoly, parameterPoint, slopeValue, mul_div_assoc, Finset.sum_div]

theorem den_constant_pos (A : AffineFractionFamily n H) (h : Fin H) :
    0 < (A.den h).coeff 0 := by
  have hp := A.den_pos h (fun _ ↦ false)
  rwa [eval_affine_zero _ (A.den_degree h)] at hp

theorem eval_denPoly (A : AffineFractionFamily n H) (t : ℝ)
    (h : Fin H) (x : Fin n → Bool) :
    eval (parameterPoint A t) (denPoly h x) =
      eval (cubePoint x) (A.den h) / (A.den h).coeff 0 := by
  simp only [denPoly, map_add, map_one, eval_linear_true]
  rw [eval_affine _ (A.den_degree h)]
  rw [add_div, div_self (den_constant_pos A h).ne']

theorem eval_denPoly_pos (A : AffineFractionFamily n H) (t : ℝ)
    (h : Fin H) (x : Fin n → Bool) :
    0 < eval (parameterPoint A t) (denPoly h x) := by
  rw [eval_denPoly]
  exact div_pos (A.den_pos h x) (den_constant_pos A h)

theorem normalized_head_eval (A : AffineFractionFamily n H) {t : ℝ} (ht : t ≠ 0)
    (h : Fin H) (x : Fin n → Bool) :
    eval (parameterPoint A t) (linearPoly false h x) /
      eval (parameterPoint A t) (denPoly h x) =
    (eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h) -
      (A.num h).coeff 0 / (A.den h).coeff 0) / t := by
  rw [eval_linear_false]
  simp only [denPoly, map_add, map_one, eval_linear_true]
  rw [eval_affine _ (A.num_degree h), eval_affine _ (A.den_degree h)]
  apply normalized_fraction _ _ _ _ _ (den_constant_pos A h).ne'
  · rw [← eval_affine _ (A.den_degree h)]
    exact (A.den_pos h x).ne'
  · exact ht

noncomputable def score (θ : Parameter n H → ℝ) (s : Bool) (x : Fin n → Bool) : ℝ :=
  (if s then 1 else -1) +
    ∑ h, eval θ (linearPoly false h x) / eval θ (denPoly h x)

theorem eval_clearedPoly (θ : Parameter n H → ℝ) (s : Bool) (x : Fin n → Bool)
    (hden : ∀ h : Fin H, eval θ (denPoly h x) ≠ 0) :
    eval θ (clearedPoly s x) = (∏ h, eval θ (denPoly h x)) * score θ s x := by
  classical
  simp only [clearedPoly, score, map_add, map_mul, map_prod, map_sum, eval_C]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro h _
    rw [← Finset.mul_prod_erase Finset.univ
      (fun g : Fin H ↦ eval θ (denPoly g x)) (Finset.mem_univ h)]
    field_simp [hden h]

/-- A strict positive-denominator affine-ratio certificate admits the exact
normalization with no additional heads. -/
theorem strictPatterns_of_affine (A : AffineFractionFamily n H) (c : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hstrict : ∀ x, if f x then
      0 < c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h)
      else c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h) < 0) :
    f ∈ strictPolynomialSignPatterns (clearedPoly (H := H) (f (fun _ ↦ false))) := by
  classical
  let t : ℝ := c + ∑ h, (A.num h).coeff 0 / (A.den h).coeff 0
  have hzero := hstrict (fun _ ↦ false)
  simp only [eval_affine_zero _ (A.num_degree _),
    eval_affine_zero _ (A.den_degree _)] at hzero
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
      score (parameterPoint A |t|) (f (fun _ ↦ false)) x =
        (c + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h)) / |t| := by
    unfold score
    rw [hsign]
    simp_rw [normalized_head_eval A ht.ne']
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    dsimp [t]
    ring
  refine ⟨parameterPoint A |t|, fun x ↦ ?_⟩
  rw [eval_clearedPoly _ _ _ (fun h ↦ (eval_denPoly_pos A |t| h x).ne'), hscore]
  have hp : 0 < ∏ h : Fin H, eval (parameterPoint A |t|) (denPoly h x) :=
    Finset.prod_pos (fun h _ ↦ eval_denPoly_pos A |t| h x)
  have hx := hstrict x
  cases hfx : f x <;> simp only [hfx, Bool.false_eq_true, ↓reduceIte] at hx ⊢
  · exact mul_neg_of_pos_of_neg hp (div_neg_of_neg_of_pos hx ht)
  · exact mul_pos hp (div_pos hx ht)

theorem mem_strictPatterns_of_computable {f : (Fin n → Bool) → Bool}
    (hf : computableWithHeadsN n H f) :
    f ∈ strictPolynomialSignPatterns (clearedPoly (H := H) (f (fun _ ↦ false))) := by
  obtain ⟨φ, c, hstrict⟩ := exists_strict_fracCertificate (fracComputable_of_computable hf)
  apply strictPatterns_of_affine (FracAtom.affineFamily φ) c f
  intro x
  simpa only [FracAtom.affineFamily, ← FracAtom.eval_eq_numPoly_div_denPoly] using hstrict x

/-- The exact dimension and degree reduction from the unchanged head model. -/
theorem card_le_two_patterns :
    (headComputableFunctions n H).ncard ≤
      (strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) false)).ncard +
      (strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) true)).ncard := by
  classical
  apply (Set.ncard_le_ncard (t :=
    strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) false) ∪
    strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) true)) ?_ (Set.toFinite _)).trans
    (Set.ncard_union_le _ _)
  intro f hf
  have hp := mem_strictPatterns_of_computable hf
  cases hzero : f (fun _ ↦ false)
  · exact Or.inl (by simpa only [hzero] using hp)
  · exact Or.inr (by simpa only [hzero] using hp)

/-- Warren's theorem applied after exact normalization. -/
theorem card_le_warren (hWarren : WarrenStrictSignPatternBound)
    (hn : 0 < n) (hH : 0 < H) (hp : 2 * n * H ≤ 2 ^ n) :
    ((headComputableFunctions n H).ncard : ℝ) ≤
      2 * (2 * Real.exp 1 * (2 : ℝ) ^ n / n) ^ (2 * n * H) := by
  have hcount (s : Bool) :
      ((strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) s)).ncard : ℝ) ≤
        (2 * Real.exp 1 * (2 : ℝ) ^ n / n) ^ (2 * n * H) := by
    have hw := hWarren (2 ^ n) H (2 * n * H) hH (by positivity) hp
      (Fin n → Bool) (Parameter n H) (clearedPoly s)
      (by simp [Fintype.card_bool]) card_parameter (clearedPoly_totalDegree_le s)
    have hb : 4 * Real.exp 1 * (H : ℝ) * ((2 ^ n : ℕ) : ℝ) / ((2 * n * H : ℕ) : ℝ) =
        2 * Real.exp 1 * (2 : ℝ) ^ n / n := by
      push_cast
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hH' : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
      field_simp
      ring
    rwa [hb] at hw
  have hc : ((headComputableFunctions n H).ncard : ℝ) ≤
      ((strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) false)).ncard : ℝ) +
      ((strictPolynomialSignPatterns (clearedPoly (n := n) (H := H) true)).ncard : ℝ) := by
    exact_mod_cast (card_le_two_patterns (n := n) (H := H))
  nlinarith [hcount false, hcount true]

/-- A convenient integer specialization retaining the denominator in Warren's
base. Its leading exponent is `2*n^2*H`, rather than the inherited coarse `35`. -/
theorem card_le_two_pow (hWarren : WarrenStrictSignPatternBound)
    (hn : 6 ≤ n) (hH : 0 < H) (hp : 2 * n * H ≤ 2 ^ n) :
    (headComputableFunctions n H).ncard ≤ 2 ^ (1 + 2 * n * n * H) := by
  have hnpos : 0 < n := by omega
  have hnreal : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : 2 * Real.exp 1 * (2 : ℝ) ^ n / n ≤ (2 : ℝ) ^ n := by
    apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hnpos)).2
    have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    have hpow : 0 ≤ (2 : ℝ) ^ n := by positivity
    nlinarith
  have hcount := card_le_warren hWarren hnpos hH hp
  have hfinal : ((headComputableFunctions n H).ncard : ℝ) ≤
      (2 : ℝ) ^ (1 + 2 * n * n * H) := by
    calc
      ((headComputableFunctions n H).ncard : ℝ) ≤
          2 * (2 * Real.exp 1 * (2 : ℝ) ^ n / n) ^ (2 * n * H) := hcount
      _ ≤ 2 * ((2 : ℝ) ^ n) ^ (2 * n * H) := by
        gcongr
      _ = (2 : ℝ) ^ (1 + 2 * n * n * H) := by
        rw [← pow_mul, pow_add, pow_one]
        congr 1
        congr 1
        ring
  exact_mod_cast hfinal

theorem worstCase_gt (hWarren : WarrenStrictSignPatternBound)
    (hn : 6 ≤ n) (hH : 0 < H)
    (hsmall : 1 + 2 * n * n * H < 2 ^ n) :
    H < worstCaseHeadComplexity n := by
  have hp : 2 * n * H ≤ 2 ^ n := by
    have hmul : 2 * n * H ≤ 2 * n * H * n := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  obtain ⟨f, hf⟩ := exists_HStar_gt_of_card_lt
    ((card_le_two_pow hWarren hn hH hp).trans_lt
      (Nat.pow_lt_pow_right (by norm_num) hsmall))
  exact hf.trans_le (HStar_le_worstCaseHeadComplexity f)

/-- The sharpened finite lower bound, conditional only on the supplied Warren
proof. The original definition of worst-case head complexity is unchanged. -/
theorem worstCase_gt_div (hWarren : WarrenStrictSignPatternBound)
    (hn : 6 ≤ n) (hsize : 2 * n * n ≤ 2 ^ n - 2) :
    (2 ^ n - 2) / (2 * n * n) < worstCaseHeadComplexity n := by
  have hd : 0 < 2 * n * n := by positivity
  have hH : 0 < (2 ^ n - 2) / (2 * n * n) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hle := (Nat.le_div_iff_mul_le hd).2 (show 1 * (2 * n * n) ≤ 2 ^ n - 2 by simpa)
    omega
  apply worstCase_gt hWarren hn hH
  have hm := Nat.div_mul_le_self (2 ^ n - 2) (2 * n * n)
  have hN : 2 ≤ 2 ^ n := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsub := Nat.sub_add_cancel hN
  nlinarith

/-- The normalized finite strict sign count, with Warren fully discharged. -/
theorem card_le (hn : 0 < n) (hH : 0 < H) (hp : 2 * n * H ≤ 2 ^ n) :
    ((headComputableFunctions n H).ncard : ℝ) ≤
      2 * (2 * Real.exp 1 * (2 : ℝ) ^ n / n) ^ (2 * n * H) :=
  card_le_warren warrenStrictSignPatternBound hn hH hp

theorem two_mul_sq_add_two_le_pow (hn : 8 ≤ n) : 2 * n * n + 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

/-- An unconditional exponential lower bound against the original definition,
valid for every input dimension at least eight. It improves the constant only. -/
theorem worstCase_gt_div_all_large (hn : 8 ≤ n) :
    (2 ^ n - 2) / (2 * n * n) < worstCaseHeadComplexity n := by
  apply worstCase_gt_div warrenStrictSignPatternBound (by omega)
  have hg := two_mul_sq_add_two_le_pow hn
  omega

/-- Real division form, exposing the leading constant one half. -/
theorem worstCase_real_lower (hn : 8 ≤ n) :
    ((2 : ℝ) ^ n - 1) / (2 * (n : ℝ) * n) ≤ (worstCaseHeadComplexity n : ℝ) := by
  have hd : 0 < 2 * n * n := by positivity
  have hlt : 2 ^ n - 2 < worstCaseHeadComplexity n * (2 * n * n) :=
    (Nat.div_lt_iff_lt_mul hd).mp (worstCase_gt_div_all_large hn)
  have hpow : 2 ≤ 2 ^ n := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnat : 2 ^ n ≤ 1 + worstCaseHeadComplexity n * (2 * n * n) := by omega
  have hreal : (2 : ℝ) ^ n ≤ 1 + (worstCaseHeadComplexity n : ℝ) * (2 * (n : ℝ) * n) := by
    exact_mod_cast hnat
  apply (div_le_iff₀ (show (0 : ℝ) < 2 * (n : ℝ) * n by positivity)).2
  linarith

end HeadComplexity.NormalizedCounting
