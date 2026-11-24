import HeadComplexity.Research.FeasibleRationalBasis
import HeadComplexity.Research.MarginCapacityEstimates
import Mathlib.Data.Nat.Choose.Bounds

set_option linter.style.header false

/-!
The missing active-chart inequality is isolated with its exact finite cost.
All chart counts retain global unit slack and the numerator coefficient box.
-/

noncomputable section
namespace HeadComplexity.FeasibleChartEntropy
open Finset MvPolynomial
open scoped BigOperators
open PartialLinearCapacity DenominatorCapacity FeasibleRationalBasis

variable {n H : ℕ}

local instance : DecidableEq (Input n) := Classical.decEq _
local instance : Fintype (Certificate (Input n) (LinearParameter n H)) := by
  classical
  infer_instance

/-- A binomial coefficient estimate obtained from one term of the exponential series. -/
theorem choose_le_exp_entropy (m l : ℕ) (hl : 0 < l) (hm : 0 < m) :
    ((m.choose l : ℕ) : ℝ) ≤
      Real.exp ((l : ℝ) * Real.log (Real.exp 1 * m / l)) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have he := Real.pow_div_factorial_le_exp (l : ℝ) hl0.le l
  have hfac : (0 : ℝ) < l.factorial := by exact_mod_cast Nat.factorial_pos l
  calc
    _ ≤ (m : ℝ) ^ l / l.factorial := Nat.choose_le_pow_div l m
    _ = ((m : ℝ) / l) ^ l * ((l : ℝ) ^ l / l.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ ((m : ℝ) / l) ^ l * Real.exp l :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = Real.exp ((l : ℝ) * Real.log (Real.exp 1 * m / l)) := by
      rw [Real.log_div (by positivity) hl0.ne',
        Real.log_mul (Real.exp_ne_zero _) hm0.ne', Real.log_exp]
      rw [show (l : ℝ) * (1 + Real.log m - Real.log l) =
        (l : ℝ) * Real.log ((m : ℝ) / l) + l by
          rw [Real.log_div hm0.ne' hl0.ne']; ring]
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity)]

/-- The unordered active row set and its selected Boolean labels cost this
many certificates. The two copies of each coefficient index are box rows. -/
theorem card_certificates_le_exp :
    (Fintype.card (Certificate (Input n) (LinearParameter n H)) : ℝ) ≤
      Real.exp (((n : ℝ) * H + 1) *
        Real.log (2 * Real.exp 1 * ((2 : ℝ) ^ n + 2 * (n * H + 1)) / (n * H + 1))) := by
  have hcard := card_certificate (ι := Input n) (κ := LinearParameter n H)
  conv_lhs at hcard => rw [Fintype.card_eq_nat_card]
  rw [Fintype.card_eq_nat_card, hcard]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, card_linearParameter,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hc := choose_le_exp_entropy (2 ^ n + 2 * (n * H + 1)) (n * H + 1)
    (by omega) (by positivity)
  push_cast at hc
  calc
    _ ≤ Real.exp (((n : ℝ) * H + 1) *
        Real.log (Real.exp 1 * ((2 : ℝ) ^ n + 2 * (n * H + 1)) / (n * H + 1))) *
        (2 : ℝ) ^ (n * H + 1) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by
      have h2 : (2 : ℝ) ^ (n * H + 1) =
          Real.exp (((n : ℝ) * H + 1) * Real.log 2) := by
        rw [show (n : ℝ) * H + 1 = ((n * H + 1 : ℕ) : ℝ) by norm_cast,
          Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [h2, ← Real.exp_add, ← mul_add]
      congr 2
      rw [← Real.log_mul (by positivity) (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      ring

/-- Uniform finite bounds on the *feasible* continuation sets give a bound on
all original truth tables, without any margin premise. -/
theorem card_original_le_exp_of_chart_bound {E : ℝ}
    (hchart : ∀ c : Certificate (Input n) (LinearParameter n H),
      ((patterns (affineDen (n := n) (H := H)) c).ncard : ℝ) ≤ Real.exp E) :
    ((headComputableFunctions n H).ncard : ℝ) ≤
      Real.exp (((n : ℝ) * H + 1) *
        Real.log (2 * Real.exp 1 * ((2 : ℝ) ^ n + 2 * (n * H + 1)) / (n * H + 1)) + E) := by
  classical
  calc
    _ ≤ ∑ c : Certificate (Input n) (LinearParameter n H),
        ((patterns (affineDen (n := n) (H := H)) c).ncard : ℝ) := by
      exact_mod_cast (card_headComputableFunctions_le_sum (n := n) (H := H))
    _ ≤ ∑ _c : Certificate (Input n) (LinearParameter n H), Real.exp E :=
      sum_le_sum fun c _ => hchart c
    _ = (Fintype.card (Certificate (Input n) (LinearParameter n H)) : ℝ) * Real.exp E := by simp
    _ ≤ Real.exp (((n : ℝ) * H + 1) *
        Real.log (2 * Real.exp 1 * ((2 : ℝ) ^ n + 2 * (n * H + 1)) / (n * H + 1))) * Real.exp E :=
      mul_le_mul_of_nonneg_right card_certificates_le_exp (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

/-- The active-certificate entropy plus a continuation budget is below a fixed
fraction of the full truth-table entropy. -/
theorem certificate_entropy_at_budget {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hbudget : (n : ℝ) * H + 1 ≤ (2 : ℝ) ^ n / (25 * t)) :
    ((n : ℝ) * H + 1) *
      Real.log (2 * Real.exp 1 * ((2 : ℝ) ^ n + 2 * (n * H + 1)) / (n * H + 1)) +
      ((n : ℝ) * H + 1) * t ≤ 8 * (2 : ℝ) ^ n / 25 := by
  have hr : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have ht1 : 1 ≤ t := by
    apply le_trans _ htlo
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hp0 : 0 < (n : ℝ) * H + 1 := by positivity
  have hpN : 2 * ((n : ℝ) * H + 1) ≤ (2 : ℝ) ^ n := by
    have hh := (le_div_iff₀ (by linarith : 0 < 25 * t)).mp hbudget
    nlinarith
  have he := MarginCapacityEstimates.entropy_bound (K := 0) hr (by positivity)
    (le_refl 0) hp0 (by norm_num : (0 : ℝ) < 1) htlo hthi
    (by positivity) hbudget (by
      have hx : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr (by linarith)
      nlinarith : (1 : ℝ) ≤ 6 * ((n : ℝ) + 1) * Real.exp t)
  simp only [zero_mul, zero_add, mul_one] at he
  have harg : 2 * Real.exp 1 * ((2 : ℝ) ^ n + 2 * (n * H + 1)) / (n * H + 1) ≤
      4 * Real.exp 1 * (2 : ℝ) ^ n / (n * H + 1) := by
    apply div_le_div_of_nonneg_right _ hp0.le
    have hh := mul_le_mul_of_nonneg_left hpN (by positivity : 0 ≤ 2 * Real.exp 1)
    nlinarith
  have hlog := Real.log_le_log (by positivity) harg
  have hcert := mul_le_mul_of_nonneg_left hlog hp0.le
  have hchartE : ((n : ℝ) * H + 1) * t ≤ (2 : ℝ) ^ n / 25 := by
    have hh := (le_div_iff₀ (by linarith : 0 < 25 * t)).mp hbudget
    nlinarith
  linarith

/-- At the critical parameter budget, a per-chart entropy of at most `L*t`
leaves the total exponent below half the truth-table exponent. -/
theorem card_original_le_exp_at_budget {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hbudget : (n : ℝ) * H + 1 ≤ (2 : ℝ) ^ n / (25 * t))
    (hchart : ∀ c : Certificate (Input n) (LinearParameter n H),
      ((patterns (affineDen (n := n) (H := H)) c).ncard : ℝ) ≤
        Real.exp (((n : ℝ) * H + 1) * t)) :
    ((headComputableFunctions n H).ncard : ℝ) ≤
      Real.exp (8 * (2 : ℝ) ^ n / 25) := by
  exact (card_original_le_exp_of_chart_bound hchart).trans
    (Real.exp_le_exp.mpr (certificate_entropy_at_budget hn htlo hthi hbudget))

/-- Strictly fewer than all original truth tables follow from the indicated
feasible-chart count; the chart count itself is an explicit missing premise. -/
theorem worstCase_gt_of_card_le_exp
    (hc : ((headComputableFunctions n H).ncard : ℝ) ≤
      Real.exp (8 * (2 : ℝ) ^ n / 25)) : H < worstCaseHeadComplexity n := by
  have hstrict : ((headComputableFunctions n H).ncard : ℝ) < (2 : ℝ) ^ (2 ^ n) := by
    calc
      _ ≤ _ := hc
      _ < Real.exp (((2 ^ n : ℕ) : ℝ) * Real.log 2) := by
        apply Real.exp_lt_exp.mpr
        push_cast
        have hN : (0 : ℝ) < 2 ^ n := by positivity
        have hh := mul_lt_mul_of_pos_right Real.log_two_gt_d9
          (by positivity : (0 : ℝ) < 2 ^ n)
        nlinarith
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hnat : (headComputableFunctions n H).ncard < 2 ^ (2 ^ n) := by exact_mod_cast hstrict
  obtain ⟨f, hf⟩ := exists_HStar_gt_of_card_lt hnat
  exact hf.trans_le (HStar_le_worstCaseHeadComplexity f)


theorem worstCase_gt_of_chart_entropy {t : ℝ} (hn : 32 ≤ n)
    (htlo : Real.log ((n : ℝ) + 1) ≤ t) (hthi : t ≤ n)
    (hbudget : (n : ℝ) * H + 1 ≤ (2 : ℝ) ^ n / (25 * t))
    (hchart : ∀ c : Certificate (Input n) (LinearParameter n H),
      ((patterns (affineDen (n := n) (H := H)) c).ncard : ℝ) ≤
        Real.exp (((n : ℝ) * H + 1) * t)) :
    H < worstCaseHeadComplexity n := by
  exact worstCase_gt_of_card_le_exp
    (card_original_le_exp_at_budget hn htlo hthi hbudget hchart)

theorem worstCase_gt_of_sqrt_chart_entropy (hn : 32 ≤ n)
    (hbudget : (n : ℝ) * H + 1 ≤ (2 : ℝ) ^ n / (25 * Real.sqrt n))
    (hchart : ∀ c : Certificate (Input n) (LinearParameter n H),
      ((patterns (affineDen (n := n) (H := H)) c).ncard : ℝ) ≤
        Real.exp (((n : ℝ) * H + 1) * Real.sqrt n)) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_chart_entropy hn (MarginCapacityEstimates.sqrt_test_range hn).1
    (MarginCapacityEstimates.sqrt_test_range hn).2 hbudget hchart

theorem worstCase_gt_of_logarithmic_chart_entropy (hn : 32 ≤ n)
    (hbudget : (n : ℝ) * H + 1 ≤ (2 : ℝ) ^ n / (25 * ((n : ℝ) / Real.log n)))
    (hchart : ∀ c : Certificate (Input n) (LinearParameter n H),
      ((patterns (affineDen (n := n) (H := H)) c).ncard : ℝ) ≤
        Real.exp (((n : ℝ) * H + 1) * ((n : ℝ) / Real.log n))) :
    H < worstCaseHeadComplexity n :=
  worstCase_gt_of_chart_entropy hn (MarginCapacityEstimates.logarithmic_test_range hn).1
    (MarginCapacityEstimates.logarithmic_test_range hn).2 hbudget hchart

end HeadComplexity.FeasibleChartEntropy
