import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option linter.style.header false

/-!
The exact geometric approximation and sign-preservation step used in
margin_sensitive_polynomial_capacity.md.  No margin repair or unrestricted
head lower bound is asserted here.
-/
noncomputable section

namespace HeadComplexity.ConditionedReciprocalApproximation

open Finset
open scoped BigOperators

theorem selected_max_sum_bounds {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (j : ι) (hnonneg : ∀ i, 0 ≤ v i)
    (hmax : ∀ i, v i ≤ v j) :
    v j ≤ ∑ i, v i ∧ (∑ i, v i) ≤ (Fintype.card ι : ℝ)*v j := by
  constructor
  · exact single_le_sum (fun i _ => hnonneg i) (mem_univ j)
  · calc
      (∑ i, v i) ≤ ∑ _i : ι, v j := sum_le_sum (fun i _ => hmax i)
      _ = (Fintype.card ι : ℝ)*v j := by simp [nsmul_eq_mul]

def headApprox (A B q m : ℝ) (d : ℕ) : ℝ :=
  A / (m*q) * ∑ k ∈ range (d+1), (1-B/(m*q))^k

theorem exact_error (A B q m : ℝ) (d : ℕ)
    (hB : B ≠ 0) (hq : q ≠ 0) (hm : m ≠ 0) :
    A/B-headApprox A B q m d = A/B*(1-B/(m*q))^(d+1) := by
  induction d with
  | zero =>
      simp only [headApprox, zero_add, sum_range_one, pow_zero, mul_one, pow_one]
      field_simp
  | succ d ih =>
      simp only [headApprox] at ih ⊢
      rw [sum_range_succ, mul_add]
      rw [show A/B-(A/(m*q)*(∑ k ∈ range (d+1), (1-B/(m*q))^k) +
        A/(m*q)*(1-B/(m*q))^(d+1)) =
        (A/B-A/(m*q)*(∑ k ∈ range (d+1), (1-B/(m*q))^k)) -
        A/(m*q)*(1-B/(m*q))^(d+1) by ring]
      rw [ih]
      have hc : A/B-A/(m*q) = A/B*(1-B/(m*q)) := by field_simp
      calc
        _ = (A/B-A/(m*q))*(1-B/(m*q))^(d+1) := by ring
        _ = A/B*(1-B/(m*q))*(1-B/(m*q))^(d+1) := by rw [hc]
        _ = _ := by rw [pow_succ]; ring

theorem geometric_relative_error (A B q m : ℝ) (d : ℕ)
    (hq : 0 < q) (hm : 1 ≤ m) (hlo : q ≤ B) (hhi : B ≤ m * q) :
    |A/B-headApprox A B q m d| ≤ |A/B| *(1-1/m)^(d+1) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hB : 0 < B := lt_of_lt_of_le hq hlo
  have hmq : 0 < m*q := mul_pos hm0 hq
  have hr0 : 0 ≤ 1-B/(m*q) := by
    have : B/(m*q) ≤ 1 := (div_le_one hmq).2 hhi
    linarith
  have hr : 1-B/(m*q) ≤ 1-1/m := by
    have : 1/m ≤ B/(m*q) := by
      apply (div_le_div_iff₀ hm0 hmq).2
      nlinarith
    linarith
  rw [exact_error A B q m d (ne_of_gt hB) (ne_of_gt hq) (ne_of_gt hm0), abs_mul,
    abs_of_nonneg (pow_nonneg hr0 _)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr _) (abs_nonneg _)

theorem exponential_relative_error (A B q m : ℝ) (d : ℕ)
    (hq : 0 < q) (hm : 1 ≤ m) (hlo : q ≤ B) (hhi : B ≤ m * q) :
    |A/B-headApprox A B q m d| ≤ |A/B| *Real.exp (-((d+1 : ℕ) : ℝ)/m) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hr0 : 0 ≤ 1-1/m := by
    have : 1/m ≤ 1 := (div_le_one hm0).2 hm
    linarith
  have hr : 1-1/m ≤ Real.exp (-1/m) := by
    simpa only [neg_div, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-1/m)
  have hp := pow_le_pow_left₀ hr0 hr (d+1)
  have he : Real.exp (-1/m)^(d+1) = Real.exp (-((d+1 : ℕ) : ℝ)/m) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hp
  exact (geometric_relative_error A B q m d hq hm hlo hhi).trans
    (mul_le_mul_of_nonneg_left hp (abs_nonneg _))

theorem sign_preserved_of_relative_error {ι : Type*} [Fintype ι]
    (a g M : ι → ℝ) (c F gamma : ℝ)
    (hF : |F| = 1) (hgamma : 0 < gamma)
    (hM : 0 < |c| + ∑ h, M h)
    (hmargin : gamma * (|c| + ∑ h, M h) ≤ F * (c + ∑ h, a h))
    (herror : ∀ h, |a h - g h| ≤ gamma / 2 * M h) :
    0 < F*(c+∑ h, g h) := by
  have herr : |(c+∑ h, a h)-(c+∑ h, g h)| ≤ gamma/2*(∑ h, M h) := by
    rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
    calc
      |∑ h, (a h-g h)| ≤ ∑ h, |a h-g h| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ h, gamma/2*M h := sum_le_sum (fun h _ => herror h)
      _ = gamma/2*(∑ h, M h) := (mul_sum _ _ _).symm
  have herr' : |F*((c+∑ h, a h)-(c+∑ h, g h))| ≤ gamma/2*(∑ h, M h) := by
    simpa only [abs_mul, hF, one_mul] using herr
  have hupper := (abs_le.mp herr').2
  have hpositive : 0 < gamma*(|c|+∑ h, M h) := mul_pos hgamma hM
  have hc : 0 ≤ gamma*|c| := mul_nonneg (le_of_lt hgamma) (abs_nonneg _)
  nlinarith

theorem conditioned_score_preserves_sign {ι : Type*} [Fintype ι]
    (A B q M : ι → ℝ) (c F gamma m : ℝ) (d : ℕ)
    (hF : |F| = 1) (hgamma : 0 < gamma) (hm : 1 ≤ m)
    (hq : ∀ h, 0 < q h) (hlo : ∀ h, q h ≤ B h)
    (hhi : ∀ h, B h ≤ m * q h)
    (hamp : ∀ h, |A h / B h| ≤ M h)
    (hM : 0 < |c| + ∑ h, M h)
    (hmargin : gamma * (|c| + ∑ h, M h) ≤ F * (c + ∑ h, A h / B h))
    (hdegree : Real.exp (-((d + 1 : ℕ) : ℝ) / m) ≤ gamma / 2) :
    0 < F*(c+∑ h, headApprox (A h) (B h) (q h) m d) := by
  apply sign_preserved_of_relative_error _ _ M c F gamma hF hgamma hM hmargin
  intro h
  calc
    _ ≤ |A h/B h| *Real.exp (-((d+1 : ℕ) : ℝ)/m) :=
      exponential_relative_error _ _ _ _ _ (hq h) hm (hlo h) (hhi h)
    _ ≤ M h*(gamma/2) := mul_le_mul (hamp h) hdegree
      (le_of_lt (Real.exp_pos _)) ((abs_nonneg _).trans (hamp h))
    _ = _ := by ring

#print axioms exact_error
#print axioms geometric_relative_error
#print axioms exponential_relative_error
#print axioms sign_preserved_of_relative_error
#print axioms conditioned_score_preserves_sign

end HeadComplexity.ConditionedReciprocalApproximation
