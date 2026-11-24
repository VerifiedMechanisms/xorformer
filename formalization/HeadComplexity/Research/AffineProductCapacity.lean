import HeadComplexity.Research.ApproximateMarginCounting

set_option linter.style.header false

/-!
An alternative unrestricted comparison class: sums of affine functions times
separable products. Its parameter degree is n+1, independent of the number of
terms. The compiler from original xorformers is an explicit unproved premise.
-/

noncomputable section
namespace HeadComplexity.AffineProductCapacity
open Finset MvPolynomial MarginCapacityEstimates
open scoped BigOperators

variable {n K : ℕ}

abbrev Parameter (n K : ℕ) := Unit ⊕ (Fin K × (Option (Fin n) ⊕ Fin n))

@[simp] theorem card_parameter :
    Fintype.card (Parameter n K) = 1 + (2 * n + 1) * K := by
  simp [Parameter]
  ring

def affinePoly (h : Fin K) (x : Fin n → Bool) :
    MvPolynomial (Parameter n K) ℝ :=
  X (Sum.inr (h, Sum.inl none)) +
    ∑ i, C (boolToReal (x i)) * X (Sum.inr (h, Sum.inl (some i)))

def productPoly (h : Fin K) (x : Fin n → Bool) :
    MvPolynomial (Parameter n K) ℝ :=
  ∏ i, if x i then X (Sum.inr (h, Sum.inr i)) else 1

def scorePoly (x : Fin n → Bool) : MvPolynomial (Parameter n K) ℝ :=
  X (Sum.inl ()) + ∑ h, affinePoly h x * productPoly h x

theorem affinePoly_totalDegree_le (h : Fin K) (x : Fin n → Bool) :
    (affinePoly h x).totalDegree ≤ 1 := by
  unfold affinePoly
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

theorem productPoly_totalDegree_le (h : Fin K) (x : Fin n → Bool) :
    (productPoly h x).totalDegree ≤ n := by
  unfold productPoly
  refine (totalDegree_finsetProd _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i _
      split <;> simp
    _ = n := by simp

theorem scorePoly_totalDegree_le (x : Fin n → Bool) :
    (scorePoly (K := K) x).totalDegree ≤ n + 1 := by
  unfold scorePoly
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro h _
  exact (totalDegree_mul _ _).trans
    ((Nat.add_le_add (affinePoly_totalDegree_le h x)
      (productPoly_totalDegree_le h x)).trans_eq (by omega))

def represented (n K : ℕ) : Set ((Fin n → Bool) → Bool) :=
  strictPolynomialSignPatterns (scorePoly (n := n) (K := K))

def parameterPoint (b : ℝ) (a : Fin K → Option (Fin n) → ℝ)
    (z : Fin K → Fin n → ℝ) : Parameter n K → ℝ
  | Sum.inl _ => b
  | Sum.inr (h, Sum.inl i) => a h i
  | Sum.inr (h, Sum.inr i) => z h i

theorem eval_scorePoly (b : ℝ) (a : Fin K → Option (Fin n) → ℝ)
    (z : Fin K → Fin n → ℝ) (x : Fin n → Bool) :
    eval (parameterPoint b a z) (scorePoly x) =
      b + ∑ h, (a h none + ∑ i, boolToReal (x i) * a h (some i)) *
        (∏ i, if x i then z h i else 1) := by
  simp only [scorePoly, affinePoly, productPoly, map_add, map_sum, map_mul,
    map_prod, eval_X, eval_C, parameterPoint]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp [parameterPoint]

/-- Positivity of the separable factors is not required by the upper count. -/
theorem mem_represented_of_score (b : ℝ) (a : Fin K → Option (Fin n) → ℝ)
    (z : Fin K → Fin n → ℝ) (f : (Fin n → Bool) → Bool)
    (hstrict : ∀ x, if f x then
      0 < b + ∑ h, (a h none + ∑ i, boolToReal (x i) * a h (some i)) *
        (∏ i, if x i then z h i else 1)
      else b + ∑ h, (a h none + ∑ i, boolToReal (x i) * a h (some i)) *
        (∏ i, if x i then z h i else 1) < 0) :
    f ∈ represented n K := by
  refine ⟨parameterPoint b a z, fun x ↦ ?_⟩
  simpa only [eval_scorePoly] using hstrict x

/-- The finite, margin-free count has degree n+1 rather than degree K. -/
theorem card_represented_le (hparameters : 1 + (2 * n + 1) * K ≤ 2 ^ n) :
    ((represented n K).ncard : ℝ) ≤
      (4 * Real.exp 1 * ((n : ℝ) + 1) * (2 : ℝ) ^ n /
        (1 + (2 * (n : ℝ) + 1) * K)) ^ (1 + (2 * n + 1) * K) := by
  have h := warrenStrictSignPatternBound (2 ^ n) (n + 1)
    (1 + (2 * n + 1) * K) (by omega) (by omega) hparameters
    (Fin n → Bool) (Parameter n K) scorePoly
    (by simp [Fintype.card_bool]) card_parameter scorePoly_totalDegree_le
  exact_mod_cast h

/-- An explicit comparison class occupying at most half the table exponent. -/
theorem card_represented_le_half_tables (hn : 32 ≤ n)
    (hwidth : (K : ℝ) ≤ (2 : ℝ) ^ n /
      (100 * n * Real.log ((n : ℝ) + 1))) :
    (represented n K).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  let t := Real.log ((n : ℝ) + 1)
  have hr : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : 1 ≤ t := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hthi : t ≤ n := by
    simpa only [t, add_sub_cancel_right] using
      Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  have hoverhead : 500 * ((0 : ℝ) + 1) * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by
    simpa using (show (500 : ℝ) * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n by
      exact_mod_cast quadratic_le_two_pow hn)
  have hb := head_overhead_budgets hr (by positivity) (le_refl (0 : ℝ)) ht1 hthi
    hoverhead (hwidth.trans (by linarith :
      (2 : ℝ) ^ n / (100 * n * t) ≤ (2 : ℝ) ^ n / (100 * n * t) + (0 + 1)))
  have hp : 1 + (2 * (n : ℝ) + 1) * K ≤ (2 : ℝ) ^ n / (25 * t) := by
    have hk : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
    nlinarith [hb.2]
  have hparam : 1 + (2 * n + 1) * K ≤ 2 ^ n := by
    have hd : (2 : ℝ) ^ n / (25 * t) ≤ (2 : ℝ) ^ n :=
      div_le_self (by positivity) (by linarith)
    exact_mod_cast hp.trans hd
  have hentropy := entropy_bound (K := 0) hr (by positivity) (le_refl 0)
    (by positivity : (0 : ℝ) < 1 + (2 * (n : ℝ) + 1) * K)
    (by positivity : (0 : ℝ) < (n : ℝ) + 1)
    (le_refl t) hthi (by positivity) hp
    (by
      have he : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr (by linarith)
      nlinarith : (n : ℝ) + 1 ≤ 6 * ((n : ℝ) + 1) * Real.exp t)
  simp only [zero_mul, zero_add] at hentropy
  have hcount : ((represented n K).ncard : ℝ) ≤ Real.exp (7 * (2 : ℝ) ^ n / 25) := by
    calc
      _ ≤ _ := card_represented_le hparam
      _ = Real.exp ((1 + (2 * (n : ℝ) + 1) * K) *
          Real.log (4 * Real.exp 1 * ((n : ℝ) + 1) * (2 : ℝ) ^ n /
            (1 + (2 * (n : ℝ) + 1) * K))) := by
        rw [show 1 + (2 * (n : ℝ) + 1) * K =
          ((1 + (2 * n + 1) * K : ℕ) : ℝ) by norm_cast,
          Real.exp_nat_mul, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr hentropy
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have hlog : (14 : ℝ) / 25 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexp : 7 * (2 : ℝ) ^ n / 25 ≤ ((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2 := by
    rw [hpow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hlog (show 0 ≤ (2 : ℝ) ^ (n - 1) by positivity)]
  have hreal : ((represented n K).ncard : ℝ) ≤ (2 : ℝ) ^ (2 ^ (n - 1)) := by
    calc
      _ ≤ _ := hcount
      _ ≤ Real.exp (((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast hreal

/-- A compiler premise; it is not asserted for the original model. -/
def HasCompiler (n H K : ℕ) : Prop := headComputableFunctions n H ⊆ represented n K

theorem worstCase_gt_of_compiler {H : ℕ} (hn : 32 ≤ n)
    (hwidth : (K : ℝ) ≤ (2 : ℝ) ^ n /
      (100 * n * Real.log ((n : ℝ) + 1)))
    (hcompiler : HasCompiler n H K) : H < worstCaseHeadComplexity n := by
  have hc := Set.ncard_le_ncard hcompiler
  have hh := card_represented_le_half_tables hn hwidth
  have hstrict : (2 : ℕ) ^ (2 ^ (n - 1)) < 2 ^ (2 ^ n) := by
    apply Nat.pow_lt_pow_right (by omega)
    apply Nat.pow_lt_pow_right (by omega)
    omega
  obtain ⟨f, hf⟩ := exists_HStar_gt_of_card_lt (hc.trans_lt (hh.trans_lt hstrict))
  exact hf.trans_le (HStar_le_worstCaseHeadComplexity f)

/-- A distributional compiler may change at most the prescribed number of labels. -/
def HasApproximateCompiler (n H K r : ℕ) : Prop :=
  ∀ f, computableWithHeadsN n H f → ∃ g,
    g ∈ represented n K ∧ hammingDist f g ≤ r

/-- The same alternative count works with one-sixteenth errors. -/
theorem worstCase_gt_of_approximate_compiler {H : ℕ} (hn : 32 ≤ n)
    (hwidth : (K : ℝ) ≤ (2 : ℝ) ^ n /
      (100 * n * Real.log ((n : ℝ) + 1)))
    (hcompiler : HasApproximateCompiler n H K (2 ^ (n - 4))) :
    H < worstCaseHeadComplexity n := by
  classical
  let G := (represented n K).toFinset
  have hm : 0 < (2 : ℕ) ^ (n - 4) := by positivity
  have hN : (2 : ℕ) ^ n = 16 * 2 ^ (n - 4) := by
    rw [show n = 4 + (n - 4) by omega, pow_add]
    norm_num
  have hhalf : (2 : ℕ) ^ (n - 1) = 8 * 2 ^ (n - 4) := by
    rw [show n - 1 = 3 + (n - 4) by omega, pow_add]
    norm_num
  have hG : G.card ≤ 2 ^ (8 * 2 ^ (n - 4)) := by
    simpa only [G, ← Set.ncard_eq_toFinset_card', hhalf] using
      card_represented_le_half_tables hn hwidth
  have hc : (ApproximateMarginCounting.nearbyTables G (2 ^ (n - 4))).card <
      2 ^ (2 ^ n) := by
    rw [hN]
    apply ApproximateMarginCounting.card_nearbyTables_lt hm _ G hG
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hN
  have hsub : headComputableFunctions n H ⊆
      (ApproximateMarginCounting.nearbyTables G (2 ^ (n - 4)) :
        Set ((Fin n → Bool) → Bool)) := by
    intro f hf
    obtain ⟨g, hg, hdist⟩ := hcompiler f hf
    change f ∈ ApproximateMarginCounting.nearbyTables G (2 ^ (n - 4))
    simp only [ApproximateMarginCounting.nearbyTables, Finset.mem_biUnion]
    refine ⟨g, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩⟩
    exact Set.mem_toFinset.mpr hg
  have hcount : (headComputableFunctions n H).ncard < 2 ^ (2 ^ n) :=
    (Set.ncard_le_ncard hsub).trans_lt (by simpa using hc)
  obtain ⟨f, hf⟩ := exists_HStar_gt_of_card_lt hcount
  exact hf.trans_le (HStar_le_worstCaseHeadComplexity f)

end HeadComplexity.AffineProductCapacity
