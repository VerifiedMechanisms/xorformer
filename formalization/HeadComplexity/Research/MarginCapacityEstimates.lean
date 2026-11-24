import HeadComplexity.Research.OriginalMarginCapacity

set_option linter.style.header false

/-!
Explicit numerical estimates for the original-model finite margin count.
These statements continue to count only targets having a representation
with the specified relative margin.
-/

noncomputable section

namespace HeadComplexity.MarginCapacityEstimates

open Finset
open scoped BigOperators
open OriginalMarginCapacity RelativeMarginQuantifiers

variable {n H : ℕ}

/-- Elementary monotonicity of the entropy expression, proved without
calculus from `log r ≤ r - 1`. -/
theorem mul_log_div_le {A p P : ℝ} (hp : 0 < p) (hP : 0 < P)
    (hpP : p ≤ P) (hA : Real.exp 1 * P ≤ A) :
    p * Real.log (A / p) ≤ P * Real.log (A / P) := by
  have hApos : 0 < A := (mul_pos (Real.exp_pos 1) hP).trans_le hA
  have hL : 1 ≤ Real.log (A / P) :=
    (Real.le_log_iff_exp_le (div_pos hApos hP)).mpr ((le_div_iff₀ hP).mpr hA)
  have hsplit : A / p = (A / P) * (P / p) := by field_simp
  rw [hsplit, Real.log_mul (div_pos hApos hP).ne' (div_pos hP hp).ne', mul_add]
  calc
    _ ≤ p * Real.log (A / P) + p * (P / p - 1) := by
      gcongr
      exact Real.log_le_sub_one_of_pos (div_pos hP hp)
    _ = p * Real.log (A / P) + P - p := by field_simp; ring
    _ ≤ P * Real.log (A / P) := by nlinarith

/-- An exponential form of the finite formula, using the elementary
factorial bound rather than an asymptotic estimate. -/
theorem card_highMarginFunctions_le_exp
    {gamma : ℝ} (hgamma : 0 < gamma) (d : ℕ)
    (hdegree : Real.exp (-((d + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ≤ gamma / 2)
    (hparameters : 1 + 3 * (n + 1) * H ≤ 2 ^ n) :
    ((highMarginFunctions n H gamma).ncard : ℝ) ≤
      Real.exp ((H : ℝ) * (Real.log 2 + (n + 1) * Real.log (n + 1)) +
        (1 + 3 * (n + 1) * H) *
          Real.log (4 * Real.exp 1 * (2 * (d : ℝ) + 2) * (2 : ℝ) ^ n /
            (1 + 3 * (n + 1) * H))) := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfact : ((n + 1).factorial : ℝ) ≤ ((n : ℝ) + 1) ^ (n + 1) := by
    exact_mod_cast Nat.factorial_le_pow (n + 1)
  have hchart : (((2 * (n + 1).factorial : ℕ) : ℝ) ^ H) ≤
      Real.exp ((H : ℝ) * (Real.log 2 + (n + 1) * Real.log (n + 1))) := by
    rw [Real.exp_nat_mul, Real.exp_add]
    have he : Real.exp (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) =
        ((n : ℝ) + 1) ^ (n + 1) := by
      rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast,
        Real.exp_nat_mul, Real.exp_log (by positivity)]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2), he]
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    exact mul_le_mul_of_nonneg_left hfact (by norm_num)
  have hpower :
      (4 * Real.exp 1 * (2 * (d : ℝ) + 2) * (2 : ℝ) ^ n /
        (1 + 3 * ((n : ℝ) + 1) * H)) ^ (1 + 3 * (n + 1) * H) =
      Real.exp ((1 + 3 * ((n : ℝ) + 1) * H) *
        Real.log (4 * Real.exp 1 * (2 * (d : ℝ) + 2) * (2 : ℝ) ^ n /
          (1 + 3 * ((n : ℝ) + 1) * H))) := by
    rw [show (1 + 3 * ((n : ℝ) + 1) * H) = ((1 + 3 * (n + 1) * H : ℕ) : ℝ)
      by norm_cast, Real.exp_nat_mul, Real.exp_log (by positivity)]
  calc
    _ ≤ _ := card_highMarginFunctions_le_warren warrenStrictSignPatternBound
      hgamma d hdegree hparameters
    _ ≤ Real.exp ((H : ℝ) * (Real.log 2 + (n + 1) * Real.log (n + 1))) *
        (4 * Real.exp 1 * (2 * (d : ℝ) + 2) * (2 : ℝ) ^ n /
          (1 + 3 * ((n : ℝ) + 1) * H)) ^ (1 + 3 * (n + 1) * H) := by
      exact mul_le_mul_of_nonneg_right hchart (by positivity)
    _ = _ := by rw [hpower, ← Real.exp_add]

/-- The double-exponential test margin. -/
def testMargin (t : ℝ) : ℝ := Real.exp (-Real.exp t)

theorem testMargin_pos (t : ℝ) : 0 < testMargin t := Real.exp_pos _

theorem log_two_div_testMargin (t : ℝ) :
    Real.log (2 / testMargin t) = Real.log 2 + Real.exp t := by
  rw [testMargin, Real.log_div (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- The ceiling degree costs one exponential in the margin parameter. -/
theorem approximationDegree_le (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    2 * (approximationDegree n (testMargin t) : ℝ) + 2 ≤
      6 * ((n : ℝ) + 1) * Real.exp t := by
  have hm : (2 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (show 2 ≤ n + 1 by omega)
  have he : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hceil : (approximationDegree n (testMargin t) : ℝ) <
      ((n : ℝ) + 1) * (Real.log 2 + Real.exp t) + 1 := by
    unfold approximationDegree
    rw [log_two_div_testMargin]
    norm_cast at *
    exact Nat.ceil_lt_add_one (by positivity)
  have hlog1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hmE : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * Real.exp t := by
    exact le_mul_of_one_le_right (by positivity) he
  have hmL : ((n : ℝ) + 1) * Real.log 2 ≤ (n : ℝ) + 1 := by
    exact mul_le_of_le_one_right (by positivity) hlog1
  nlinarith

/-- A fully explicit finite entropy estimate. The two width budgets already
include any head overhead; no limiting argument occurs in this lemma. -/
theorem entropy_bound {r N K p D t : ℝ}
    (hr : 32 ≤ r) (hN : 0 < N) (hK : 0 ≤ K) (hp : 0 < p) (hD : 0 < D)
    (htlo : Real.log (r + 1) ≤ t) (hthi : t ≤ r)
    (hwidth : K ≤ 3 * N / (250 * r * t))
    (hparameters : p ≤ N / (25 * t))
    (hdegree : D ≤ 6 * (r + 1) * Real.exp t) :
    K * (Real.log 2 + (r + 1) * Real.log (r + 1)) +
      p * Real.log (4 * Real.exp 1 * D * N / p) ≤ 7 * N / 25 := by
  have hr0 : 0 < r := by linarith
  have hm0 : 0 < r + 1 := by linarith
  have ht1 : 1 ≤ t := by
    apply le_trans _ htlo
    apply (Real.le_log_iff_exp_le hm0).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have ht0 : 0 < t := by linarith
  have he : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht0.le
  have hlog2 : Real.log 2 ≤ t :=
    (Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ r + 1)).trans htlo
  have hlogmul : (r + 1) * Real.log (r + 1) ≤ (r + 1) * t :=
    mul_le_mul_of_nonneg_left htlo hm0.le
  have hL : Real.log 2 + (r + 1) * Real.log (r + 1) ≤ 3 * r * t := by
    nlinarith
  have hwidth' : K * (250 * r * t) ≤ 3 * N :=
    (le_div_iff₀ (by positivity)).mp hwidth
  have hchart : K * (Real.log 2 + (r + 1) * Real.log (r + 1)) ≤ 9 * N / 250 := by
    have h := mul_le_mul_of_nonneg_left hL hK
    nlinarith
  let A := 24 * Real.exp 1 * (r + 1) * Real.exp t * N
  let P := N / (25 * t)
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hP0 : 0 < P := by dsimp [P]; positivity
  have hPle : P ≤ N := div_le_self hN.le (by linarith)
  have hmE : r + 1 ≤ (r + 1) * Real.exp t := le_mul_of_one_le_right hm0.le he
  have hA : Real.exp 1 * P ≤ A := by
    calc
      _ ≤ Real.exp 1 * N := mul_le_mul_of_nonneg_left hPle (Real.exp_pos _).le
      _ ≤ A := by
        dsimp [A]
        have hscale : 1 ≤ 24 * ((r + 1) * Real.exp t) := by nlinarith
        have h := mul_le_mul_of_nonneg_left hscale (mul_pos (Real.exp_pos 1) hN).le
        nlinarith
  have hraw : 4 * Real.exp 1 * D * N ≤ A := by
    calc
      _ ≤ 4 * Real.exp 1 * (6 * (r + 1) * Real.exp t) * N := by gcongr
      _ = A := by dsimp [A]; ring
  have h600 : 600 * Real.exp 1 ≤ (r + 1) ^ 3 := by
    calc
      _ ≤ 1800 := by nlinarith [Real.exp_one_lt_three]
      _ ≤ (33 : ℝ) ^ 3 := by norm_num
      _ ≤ (r + 1) ^ 3 := by gcongr; linarith
  have harg600 : 600 * Real.exp 1 * (r + 1) * t ≤ (r + 1) ^ 5 := by
    calc
      _ ≤ (r + 1) ^ 3 * (r + 1) * (r + 1) := by gcongr; linarith
      _ = _ := by ring
  have hlog600 : Real.log (600 * Real.exp 1 * (r + 1) * t) ≤
      5 * Real.log (r + 1) := by
    have h := Real.log_le_log (by positivity) harg600
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hquot : A / P = (600 * Real.exp 1 * (r + 1) * t) * Real.exp t := by
    dsimp [A, P]
    field_simp
    ring
  have hpoly : p * Real.log (4 * Real.exp 1 * D * N / p) ≤ 6 * N / 25 := by
    calc
      _ ≤ p * Real.log (A / p) := by
        apply mul_le_mul_of_nonneg_left _ hp.le
        exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hraw hp.le)
      _ ≤ P * Real.log (A / P) := mul_log_div_le hp hP0 hparameters hA
      _ = P * (Real.log (600 * Real.exp 1 * (r + 1) * t) + t) := by
        rw [hquot, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
      _ ≤ P * (5 * Real.log (r + 1) + t) := by gcongr
      _ ≤ P * (6 * t) := by gcongr; linarith
      _ = 6 * N / 25 := by dsimp [P]; field_simp
  nlinarith

/-- At explicit width and parameter budgets, the high-margin class occupies
less than half the truth-table exponent. -/
theorem card_highMargin_test_le_exp (hn : 32 ≤ n) {t : ℝ}
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hwidth : (H : ℝ) ≤ 3 * (2 : ℝ) ^ n / (250 * n * t))
    (hparameters : (1 + 3 * ((n : ℝ) + 1) * H) ≤ (2 : ℝ) ^ n / (25 * t)) :
    ((highMarginFunctions n H (testMargin t)).ncard : ℝ) ≤
      Real.exp (7 * (2 : ℝ) ^ n / 25) := by
  have hr : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : 1 ≤ t := by
    apply le_trans _ htlo
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hparam : 1 + 3 * (n + 1) * H ≤ 2 ^ n := by
    have hdiv : (2 : ℝ) ^ n / (25 * t) ≤ (2 : ℝ) ^ n :=
      div_le_self (by positivity) (by linarith)
    exact_mod_cast hparameters.trans hdiv
  have hb := entropy_bound hr (by positivity) (Nat.cast_nonneg H)
    (by positivity : (0 : ℝ) < 1 + 3 * ((n : ℝ) + 1) * H)
    (by positivity : (0 : ℝ) < 2 * (approximationDegree n (testMargin t) : ℝ) + 2)
    htlo hthi hwidth hparameters (approximationDegree_le (by omega) (by linarith))
  exact (card_highMarginFunctions_le_exp (testMargin_pos t)
    (approximationDegree n (testMargin t)) (approximationDegree_error (testMargin_pos t))
    hparam).trans (Real.exp_le_exp.mpr hb)

/-- Natural-number version of the desired count `2^(N/2)`, since
`2^(n-1) = N/2` for the positive input dimensions in this theorem. -/
theorem card_highMargin_test_le_half_tables (hn : 32 ≤ n) {t : ℝ}
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hwidth : (H : ℝ) ≤ 3 * (2 : ℝ) ^ n / (250 * n * t))
    (hparameters : (1 + 3 * ((n : ℝ) + 1) * H) ≤ (2 : ℝ) ^ n / (25 * t)) :
    (highMarginFunctions n H (testMargin t)).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  have hcount := card_highMargin_test_le_exp hn htlo hthi hwidth hparameters
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have hlog : (14 : ℝ) / 25 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexp : 7 * (2 : ℝ) ^ n / 25 ≤ ((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2 := by
    rw [hpow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hlog (show 0 ≤ (2 : ℝ) ^ (n - 1) by positivity)]
  have hreal : ((highMarginFunctions n H (testMargin t)).ncard : ℝ) ≤
      (2 : ℝ) ^ (2 ^ (n - 1)) := by
    calc
      _ ≤ _ := hcount
      _ ≤ Real.exp (((2 ^ (n - 1) : ℕ) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast hreal

/-- Explicit arithmetic that absorbs a fixed additive head overhead. -/
theorem head_overhead_budgets {r N K B t : ℝ}
    (hr : 32 ≤ r) (hN : 0 < N) (hB : 0 ≤ B) (ht : 1 ≤ t) (hthi : t ≤ r)
    (hoverhead : 500 * (B + 1) * r ^ 2 ≤ N)
    (hK : K ≤ N / (100 * r * t) + (B + 1)) :
    K ≤ 3 * N / (250 * r * t) ∧ 1 + 3 * (r + 1) * K ≤ N / (25 * t) := by
  have hr0 : 0 < r := by linarith
  have ht0 : 0 < t := by linarith
  have hNscale : 500 * r ^ 2 ≤ N := by
    have h := mul_nonneg hB (sq_nonneg r)
    nlinarith
  have hBt : 500 * (B + 1) * r * t ≤ N := by
    calc
      _ ≤ 500 * (B + 1) * r * r := by gcongr
      _ = 500 * (B + 1) * r ^ 2 := by ring
      _ ≤ N := hoverhead
  have hadd : B + 1 ≤ N / (500 * r * t) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith [hBt])
  have hwidth : K ≤ 3 * N / (250 * r * t) := by
    calc
      _ ≤ N / (100 * r * t) + N / (500 * r * t) := hK.trans (add_le_add le_rfl hadd)
      _ = _ := by field_simp; ring
  refine ⟨hwidth, ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 25 * t)).mpr
  have hwidth' : K * (250 * r * t) ≤ 3 * N :=
    (le_div_iff₀ (by positivity)).mp hwidth
  have hscaled := mul_le_mul_of_nonneg_left hwidth' (show 0 ≤ 3 * (r + 1) by positivity)
  have hsmall : 250 * r * t ≤ N / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hthi hr0.le]
  have hcoeff : N / 2 + 9 * (r + 1) * N ≤ 10 * r * N := by
    nlinarith [mul_nonneg hN.le (show 0 ≤ r - 10 by linarith)]
  apply (mul_le_mul_iff_left₀ (show 0 < 10 * r by positivity)).mp
  nlinarith

/-- An integer estimate sufficient for the additive-overhead-free case. -/
theorem quadratic_le_two_pow (hn : 32 ≤ n) : 500 * n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hsq : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
      calc
        500 * (n + 1) ^ 2 ≤ 500 * (2 * n ^ 2) := Nat.mul_le_mul_left _ hsq
        _ = 2 * (500 * n ^ 2) := by ring
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- At width `N/(100 n t)`, both requested test-margin regimes satisfy the
half-table count as soon as `log(n+1) ≤ t ≤ n` and `n ≥ 32`. -/
theorem card_highMargin_test_at_width (hn : 32 ≤ n) {t : ℝ}
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * n * t)) :
    (highMarginFunctions n H (testMargin t)).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  have hr : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : 1 ≤ t := by
    apply le_trans _ htlo
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hoverhead : 500 * ((0 : ℝ) + 1) * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by
    simpa using (show (500 : ℝ) * (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n by
      exact_mod_cast quadratic_le_two_pow hn)
  have hb := head_overhead_budgets hr (by positivity) (le_refl (0 : ℝ)) ht1 hthi
    hoverhead (hwidth.trans (by linarith :
      (2 : ℝ) ^ n / (100 * n * t) ≤ (2 : ℝ) ^ n / (100 * n * t) + (0 + 1)))
  exact card_highMargin_test_le_half_tables hn htlo hthi hb.1 hb.2

/-- Multiplicative and additive overhead are paid before applying the count.
The comparison width can be a ceiling, since its extra one is explicit. -/
theorem card_highMargin_test_with_overhead {K B : ℕ} {C t : ℝ}
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * C * n * t))
    (hK : (K : ℝ) ≤ C * H + B + 1) :
    (highMarginFunctions n K (testMargin t)).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
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
  exact card_highMargin_test_le_half_tables hn htlo hthi hb.1 hb.2

/-- A convenient elementary logarithm estimate on the dimensions used here. -/
theorem log_add_one_le_sqrt {r : ℝ} (hr : 16 ≤ r) :
    Real.log (r + 1) ≤ Real.sqrt r := by
  have hr0 : 0 ≤ r := by linarith
  have hs0 := Real.sqrt_nonneg r
  have hs4 : 4 ≤ Real.sqrt r := by
    have h := Real.sqrt_le_sqrt hr
    norm_num at h
    exact h
  have he := Real.sum_le_exp_of_nonneg hs0 4
  norm_num [Finset.sum_range_succ] at he
  have hcube : 0 ≤ (Real.sqrt r) ^ 2 * (Real.sqrt r - 3) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  apply (Real.log_le_iff_le_exp (by linarith : 0 < r + 1)).mpr
  nlinarith [Real.sq_sqrt hr0]

theorem sqrt_test_range (hn : 32 ≤ n) :
    Real.log ((n : ℝ) + 1) ≤ Real.sqrt n ∧ Real.sqrt n ≤ n := by
  have hr : (32 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨log_add_one_le_sqrt (by linarith), Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))⟩

theorem logarithmic_test_range (hn : 32 ≤ n) :
    Real.log ((n : ℝ) + 1) ≤ (n : ℝ) / Real.log n ∧ (n : ℝ) / Real.log n ≤ n := by
  have hr : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog1 : 1 ≤ Real.log (n : ℝ) := by
    apply (Real.le_log_iff_exp_le hn0).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hlog0 : 0 < Real.log (n : ℝ) := by linarith
  have hs := (sqrt_test_range hn).1
  have hlog : Real.log (n : ℝ) ≤ Real.sqrt n :=
    (Real.log_le_log hn0 (by linarith : (n : ℝ) ≤ n + 1)).trans hs
  have hroot : Real.sqrt n ≤ (n : ℝ) / Real.log n := by
    apply (le_div_iff₀ hlog0).mpr
    calc
      _ ≤ Real.sqrt n * Real.sqrt n :=
        mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg _)
      _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
  exact ⟨hs.trans hroot, div_le_self hn0.le hlog1⟩

/-- The aimed power-scale high-margin count, fully kernel checked. -/
theorem card_highMargin_sqrt_scale (hn : 32 ≤ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * n * Real.sqrt n)) :
    (highMarginFunctions n H (Real.exp (-Real.exp (Real.sqrt n)))).ncard ≤
      2 ^ (2 ^ (n - 1)) :=
  card_highMargin_test_at_width hn (sqrt_test_range hn).1 (sqrt_test_range hn).2 hwidth

/-- The logarithmic fallback high-margin count, obtained directly from the
finite formula at `t = n / log n`. -/
theorem card_highMargin_logarithmic_scale (hn : 32 ≤ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n * Real.log n / (100 * (n : ℝ) ^ 2)) :
    (highMarginFunctions n H (Real.exp (-Real.exp ((n : ℝ) / Real.log n)))).ncard ≤
      2 ^ (2 ^ (n - 1)) := by
  apply card_highMargin_test_at_width hn (logarithmic_test_range hn).1
    (logarithmic_test_range hn).2
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog0 : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  calc
    _ ≤ _ := hwidth
    _ = _ := by field_simp

/-- The square-root test margin after a fixed factor and additive head
increase. The ceiling loss is included exactly. -/
theorem card_highMargin_sqrt_overhead {B : ℕ} {C : ℝ}
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n / (100 * C * n * Real.sqrt n)) :
    (highMarginFunctions n (⌈C * (H : ℝ)⌉₊ + B)
      (Real.exp (-Real.exp (Real.sqrt n)))).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  apply card_highMargin_test_with_overhead hn hC (sqrt_test_range hn).1
    (sqrt_test_range hn).2 hoverhead hwidth
  push_cast
  have hceil : (⌈C * (H : ℝ)⌉₊ : ℝ) < C * (H : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  linarith

/-- The logarithmic fallback test margin with all comparison-width overhead
included in the count. -/
theorem card_highMargin_logarithmic_overhead {B : ℕ} {C : ℝ}
    (hn : 32 ≤ n) (hC : 1 ≤ C)
    (hoverhead : 500 * (B + 1) * n ^ 2 ≤ 2 ^ n)
    (hwidth : (H : ℝ) ≤ (2 : ℝ) ^ n * Real.log n / (100 * C * (n : ℝ) ^ 2)) :
    (highMarginFunctions n (⌈C * (H : ℝ)⌉₊ + B)
      (Real.exp (-Real.exp ((n : ℝ) / Real.log n)))).ncard ≤ 2 ^ (2 ^ (n - 1)) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hC0 : 0 < C := by linarith
  have hlog0 : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  apply card_highMargin_test_with_overhead hn hC (logarithmic_test_range hn).1
    (logarithmic_test_range hn).2 hoverhead
  · calc
      _ ≤ _ := hwidth
      _ = _ := by field_simp
  · push_cast
    have hceil : (⌈C * (H : ℝ)⌉₊ : ℝ) < C * (H : ℝ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hC0.le (Nat.cast_nonneg _))
    linarith

#print axioms mul_log_div_le
#print axioms card_highMarginFunctions_le_exp
#print axioms approximationDegree_le
#print axioms entropy_bound
#print axioms card_highMargin_test_le_exp
#print axioms card_highMargin_test_le_half_tables
#print axioms head_overhead_budgets
#print axioms card_highMargin_test_at_width
#print axioms card_highMargin_test_with_overhead
#print axioms card_highMargin_sqrt_scale
#print axioms card_highMargin_logarithmic_scale
#print axioms card_highMargin_sqrt_overhead
#print axioms card_highMargin_logarithmic_overhead

end HeadComplexity.MarginCapacityEstimates
