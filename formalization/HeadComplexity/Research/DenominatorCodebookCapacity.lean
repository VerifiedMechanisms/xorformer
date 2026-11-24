import HeadComplexity.Research.AffineProductCapacity
import HeadComplexity.Research.NormalizedCounting

set_option linter.style.header false

/-!
A margin-free capacity bound for a fixed finite codebook of denominator
value vectors. The original-model repair to such a codebook remains an
explicit premise; numerator coefficients and cancellation remain unrestricted.
-/

noncomputable section
namespace HeadComplexity.DenominatorCodebookCapacity
open Finset MvPolynomial MarginCapacityEstimates
open scoped BigOperators

variable {n H M : ℕ}

abbrev Parameter (n H : ℕ) := Unit ⊕ (Fin H × Fin n)

@[simp] theorem card_parameter : Fintype.card (Parameter n H) = 1 + n * H := by
  simp [Parameter]
  ring

/-- Codebook values can be arbitrary reals for the upper count. -/
def scorePoly (D : Fin M → (Fin n → Bool) → ℝ) (a : Fin H → Fin M)
    (x : Fin n → Bool) : MvPolynomial (Parameter n H) ℝ :=
  X (Sum.inl ()) + ∑ h, ∑ i, C (boolToReal (x i) / D (a h) x) * X (Sum.inr (h, i))

theorem scorePoly_totalDegree_le (D : Fin M → (Fin n → Bool) → ℝ)
    (a : Fin H → Fin M) (x : Fin n → Bool) : (scorePoly D a x).totalDegree ≤ 1 := by
  unfold scorePoly
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro h _
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

def represented (D : Fin M → (Fin n → Bool) → ℝ) (H : ℕ) :
    Set ((Fin n → Bool) → Bool) :=
  ⋃ a : Fin H → Fin M, strictPolynomialSignPatterns (scorePoly D a)

def parameterPoint (b : ℝ) (c : Fin H → Fin n → ℝ) : Parameter n H → ℝ
  | Sum.inl _ => b
  | Sum.inr (h, i) => c h i

theorem eval_scorePoly (D : Fin M → (Fin n → Bool) → ℝ)
    (a : Fin H → Fin M) (b : ℝ) (c : Fin H → Fin n → ℝ) (x : Fin n → Bool) :
    eval (parameterPoint b c) (scorePoly D a x) =
      b + ∑ h, (∑ i, boolToReal (x i) * c h i) / D (a h) x := by
  simp only [scorePoly, map_add, eval_X, map_sum, map_mul, eval_C, parameterPoint]
  simp only [Finset.sum_div, div_mul_eq_mul_div]

theorem mem_represented_of_score (D : Fin M → (Fin n → Bool) → ℝ)
    (a : Fin H → Fin M) (b : ℝ) (c : Fin H → Fin n → ℝ)
    (f : (Fin n → Bool) → Bool)
    (hstrict : ∀ x, if f x then
      0 < b + ∑ h, (∑ i, boolToReal (x i) * c h i) / D (a h) x
      else b + ∑ h, (∑ i, boolToReal (x i) * c h i) / D (a h) x < 0) :
    f ∈ represented D H := by
  refine Set.mem_iUnion.mpr ⟨a, parameterPoint b c, fun x ↦ ?_⟩
  simpa only [eval_scorePoly] using hstrict x

/-- No coefficient-height or margin condition appears in the finite formula. -/
theorem card_represented_le (D : Fin M → (Fin n → Bool) → ℝ)
    (hparameters : 1 + n * H ≤ 2 ^ n) :
    ((represented D H).ncard : ℝ) ≤ (M : ℝ) ^ H *
      (4 * Real.exp 1 * (2 : ℝ) ^ n / (1 + (n : ℝ) * H)) ^ (1 + n * H) := by
  classical
  have hc (a : Fin H → Fin M) :
      ((strictPolynomialSignPatterns (scorePoly D a)).ncard : ℝ) ≤
      (4 * Real.exp 1 * (2 : ℝ) ^ n / (1 + (n : ℝ) * H)) ^ (1 + n * H) := by
    have h := warrenStrictSignPatternBound (2 ^ n) 1 (1 + n * H)
      (by omega) (by omega) hparameters (Fin n → Bool) (Parameter n H)
      (scorePoly D a) (by simp [Fintype.card_bool]) card_parameter
      (scorePoly_totalDegree_le D a)
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, mul_one] using h
  calc
    _ ≤ ∑ a : Fin H → Fin M,
        ((strictPolynomialSignPatterns (scorePoly D a)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_iUnion_le_of_fintype
        (fun a : Fin H → Fin M ↦ strictPolynomialSignPatterns (scorePoly D a))
    _ ≤ ∑ _a : Fin H → Fin M,
        (4 * Real.exp 1 * (2 : ℝ) ^ n / (1 + (n : ℝ) * H)) ^ (1 + n * H) :=
      sum_le_sum (fun a _ ↦ hc a)
    _ = _ := by simp

/-- Exact original-model affine normalization, without changing any head. -/
theorem mem_represented_of_affine (D : Fin M → (Fin n → Bool) → ℝ)
    (a : Fin H → Fin M) (A : AffineFractionFamily n H) (b : ℝ)
    (f : (Fin n → Bool) → Bool)
    (hcode : ∀ h x, D (a h) x =
      eval (cubePoint x) (A.den h) / (A.den h).coeff 0)
    (hstrict : ∀ x, if f x then
      0 < b + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h)
      else b + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h) < 0) :
    f ∈ represented D H := by
  let c : Fin H → Fin n → ℝ := fun h i ↦
    NormalizedCounting.parameterPoint A 1 (h, false, i)
  let b' := b + ∑ h, (A.num h).coeff 0 / (A.den h).coeff 0
  have heq (x : Fin n → Bool) :
      b' + ∑ h, (∑ i, boolToReal (x i) * c h i) / D (a h) x =
      b + ∑ h, eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h) := by
    have hh (h : Fin H) :
        (∑ i, boolToReal (x i) * c h i) / D (a h) x =
        eval (cubePoint x) (A.num h) / eval (cubePoint x) (A.den h) -
          (A.num h).coeff 0 / (A.den h).coeff 0 := by
      have hn := NormalizedCounting.normalized_head_eval A (by norm_num : (1 : ℝ) ≠ 0) h x
      rw [NormalizedCounting.eval_denPoly, div_one] at hn
      rw [hcode]
      simpa only [NormalizedCounting.linearPoly, map_sum, map_mul, eval_C,
        eval_X, c] using hn
    simp only [hh, Finset.sum_sub_distrib, b']
    ring
  apply mem_represented_of_score D a b' c f
  intro x
  simpa only [heq] using hstrict x

/-- A finite codebook entropy budget, independent of all score margins. -/
theorem card_represented_le_exp (D : Fin M → (Fin n → Bool) → ℝ)
    (hn : 32 ≤ n) (hM : 1 ≤ M) {t : ℝ}
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hcodebook : Real.log M ≤ n * t)
    (hwidth : (H : ℝ) ≤ 3 * (2 : ℝ) ^ n / (250 * n * t))
    (hparameters : 1 + (n : ℝ) * H ≤ (2 : ℝ) ^ n / (25 * t)) :
    ((represented D H).ncard : ℝ) ≤ Real.exp (73 * (2 : ℝ) ^ n / 250) := by
  have hr : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : 1 ≤ t := by
    apply le_trans _ htlo
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hp0 : 0 < 1 + (n : ℝ) * H := by positivity
  have hparam : 1 + n * H ≤ 2 ^ n := by
    have hd : (2 : ℝ) ^ n / (25 * t) ≤ (2 : ℝ) ^ n :=
      div_le_self (by positivity) (by linarith)
    exact_mod_cast hparameters.trans hd
  have he := entropy_bound (K := 0) hr (by positivity) (le_refl 0) hp0
    (by norm_num : (0 : ℝ) < 1) htlo hthi (by positivity) hparameters
    (by
      have hx : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr (by linarith)
      nlinarith : (1 : ℝ) ≤ 6 * ((n : ℝ) + 1) * Real.exp t)
  simp only [zero_mul, zero_add, mul_one] at he
  have hw : (H : ℝ) * (250 * n * t) ≤ 3 * (2 : ℝ) ^ n :=
    (le_div_iff₀ (by positivity)).mp hwidth
  have hbook : (H : ℝ) * Real.log M ≤ 3 * (2 : ℝ) ^ n / 250 := by
    have hh := mul_le_mul_of_nonneg_left hcodebook (Nat.cast_nonneg H)
    nlinarith
  calc
    _ ≤ _ := card_represented_le D hparam
    _ = Real.exp ((H : ℝ) * Real.log M + (1 + (n : ℝ) * H) *
          Real.log (4 * Real.exp 1 * (2 : ℝ) ^ n / (1 + (n : ℝ) * H))) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hM0]
      rw [show 1 + (n : ℝ) * H = ((1 + n * H : ℕ) : ℝ) by norm_cast,
        Real.exp_nat_mul, Real.exp_log (by positivity)]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- Codebook width and parameter budgets give the same half-table count. -/
theorem card_represented_le_half_tables (D : Fin M → (Fin n → Bool) → ℝ)
    (hn : 32 ≤ n) (hM : 1 ≤ M) {t : ℝ}
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hcodebook : Real.log M ≤ n * t)
    (hwidth : (H : ℝ) ≤ 3 * (2 : ℝ) ^ n / (250 * n * t))
    (hparameters : 1 + (n : ℝ) * H ≤ (2 : ℝ) ^ n / (25 * t)) :
    (represented D H).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  have he := card_represented_le_exp D hn hM htlo hthi hcodebook hwidth hparameters
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have hlog : (146 : ℝ) / 250 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexp : 73 * (2 : ℝ) ^ n / 250 ≤ ((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2 := by
    rw [hpow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hlog (show 0 ≤ (2 : ℝ) ^ (n - 1) by positivity)]
  have hr : ((represented D H).ncard : ℝ) ≤ (2 : ℝ) ^ (2 ^ (n - 1)) := by
    calc
      _ ≤ _ := he
      _ ≤ Real.exp (((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast hr

/-- The ceiling and additive head cost are paid in the same finite budget. -/
theorem card_represented_with_overhead (D : Fin M → (Fin n → Bool) → ℝ)
    {K B : ℕ} {C t : ℝ} (hn : 32 ≤ n) (hM : 1 ≤ M) (hC : 1 ≤ C)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hcodebook : Real.log M ≤ n * t)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * C * n * t))
    (hK : (K : ℝ) ≤ C * H + B + 1) :
    (represented D K).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  have hr : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hC0 : 0 < C := by linarith
  have ht1 : 1 ≤ t := by
    apply le_trans _ htlo
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hn0 : (0 : ℝ) < n := by positivity
  have ht0 : 0 < t := by linarith
  have hmul : C * (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * n * t) := by
    calc
      _ ≤ C * ((2 : ℝ) ^ n / (100 * C * n * t)) :=
        mul_le_mul_of_nonneg_left hwidth hC0.le
      _ = _ := by field_simp
  have hbudget : (K : ℝ) ≤ (2 : ℝ) ^ n / (100 * n * t) + ((B : ℝ) + 1) := by
    linarith
  have hoverhead' : 500 * ((B : ℝ) + 1) * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hoverhead
  have hb := head_overhead_budgets hr (by positivity) (Nat.cast_nonneg B) ht1 hthi
    hoverhead' hbudget
  apply card_represented_le_half_tables D hn hM htlo hthi hcodebook hb.1
  nlinarith [show (0 : ℝ) ≤ K by positivity]

/-- This is the missing repair hypothesis, not an asserted quantization theorem. -/
def HasCodebookRepair (D : Fin M → (Fin n → Bool) → ℝ) (H K : ℕ) : Prop :=
  headComputableFunctions n H ⊆ represented D K

/-- An original-model conclusion with the finite-codebook repair explicit. -/
theorem worstCase_gt_of_codebook_repair (D : Fin M → (Fin n → Bool) → ℝ)
    {K B : ℕ} {C t : ℝ} (hn : 32 ≤ n) (hM : 1 ≤ M) (hC : 1 ≤ C)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hcodebook : Real.log M ≤ n * t)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * C * n * t))
    (hK : (K : ℝ) ≤ C * H + B + 1)
    (hrepair : HasCodebookRepair D H K) : H < worstCaseHeadComplexity n := by
  have hc := Set.ncard_le_ncard hrepair
  have hh := card_represented_with_overhead D hn hM hC htlo hthi hcodebook
    hoverhead hwidth hK
  have hstrict : (2 : ℕ) ^ (2 ^ (n - 1)) < 2 ^ (2 ^ n) := by
    apply Nat.pow_lt_pow_right (by omega)
    apply Nat.pow_lt_pow_right (by omega)
    omega
  obtain ⟨f, hf⟩ := exists_HStar_gt_of_card_lt (hc.trans_lt (hh.trans_lt hstrict))
  exact hf.trans_le (HStar_le_worstCaseHeadComplexity f)

end HeadComplexity.DenominatorCodebookCapacity
