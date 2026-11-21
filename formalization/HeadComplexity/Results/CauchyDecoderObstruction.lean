import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# An obstruction to a four-pole Cauchy codebook

This module concerns an auxiliary decoder, not the universal head model.
Two reciprocal-square kernels cannot have strict signs positive, negative,
positive at three increasing positive addresses.
-/

namespace HeadComplexity

theorem affine_no_valley (t₀ t₁ t₂ a b : ℝ)
    (h₀₁ : t₀ ≤ t₁) (h₁₂ : t₁ ≤ t₂) :
    ¬ (0 < a + b*t₀ ∧ a + b*t₁ < 0 ∧ 0 < a + b*t₂) := by
  rintro ⟨h₀, h₁, h₂⟩
  rcases le_total 0 b with hb | hb
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr h₀₁)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr h₁₂)]

theorem positive_shift_ratio_mono (p q b c : ℝ)
    (hp : 0 < p) (hpq : p ≤ q) (hb : 0 < b) (hbc : b ≤ c) :
    (p+b)/(p+c) ≤ (q+b)/(q+c) := by
  have hc : 0 < c := hb.trans_le hbc
  have hq : 0 < q := hp.trans_le hpq
  apply (div_le_div_iff₀ (by positivity : 0 < p+c)
    (by positivity : 0 < q+c)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hbc)]

theorem positive_shift_ratio_sq_mono (p q b c : ℝ)
    (hp : 0 < p) (hpq : p ≤ q) (hb : 0 < b) (hbc : b ≤ c) :
    ((p+b)/(p+c))^2 ≤ ((q+b)/(q+c))^2 := by
  have hc : 0 < c := hb.trans_le hbc
  have hq : 0 < q := hp.trans_le hpq
  have hl := positive_shift_ratio_mono p q b c hp hpq hb hbc
  have h₀ : 0 ≤ (p+b)/(p+c) := by positivity
  have h₁ : 0 ≤ (q+b)/(q+c) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hl) (add_nonneg h₀ h₁)]

theorem two_cauchy_kernels_no_valley_ordered
    (p q r b c u v : ℝ) (hp : 0 < p) (hpq : p ≤ q)
    (hqr : q ≤ r) (hb : 0 < b) (hbc : b ≤ c) :
    ¬ (0 < u/(p+b)^2 + v/(p+c)^2 ∧
       u/(q+b)^2 + v/(q+c)^2 < 0 ∧
       0 < u/(r+b)^2 + v/(r+c)^2) := by
  have hc : 0 < c := hb.trans_le hbc
  have hq : 0 < q := hp.trans_le hpq
  have hr : 0 < r := hq.trans_le hqr
  have scale (s : ℝ) (hs : 0 < s) :
      (u/(s+b)^2 + v/(s+c)^2)*(s+b)^2 =
      u + v*((s+b)/(s+c))^2 := by
    have hsb : s+b ≠ 0 := by positivity
    have hsc : s+c ≠ 0 := by positivity
    field_simp
  rintro ⟨h₀, h₁, h₂⟩
  have h₀' := mul_pos h₀ (sq_pos_of_pos (by positivity : 0 < p+b))
  have h₁' := mul_neg_of_neg_of_pos h₁ (sq_pos_of_pos (by positivity : 0 < q+b))
  have h₂' := mul_pos h₂ (sq_pos_of_pos (by positivity : 0 < r+b))
  rw [scale p hp] at h₀'
  rw [scale q hq] at h₁'
  rw [scale r hr] at h₂'
  exact affine_no_valley _ _ _ u v
    (positive_shift_ratio_sq_mono p q b c hp hpq hb hbc)
    (positive_shift_ratio_sq_mono q r b c hq hqr hb hbc) ⟨h₀', h₁', h₂'⟩

theorem two_cauchy_kernels_no_valley
    (p q r b c u v : ℝ) (hp : 0 < p) (hpq : p ≤ q)
    (hqr : q ≤ r) (hb : 0 < b) (hc : 0 < c) :
    ¬ (0 < u/(p+b)^2 + v/(p+c)^2 ∧
       u/(q+b)^2 + v/(q+c)^2 < 0 ∧
       0 < u/(r+b)^2 + v/(r+c)^2) := by
  rcases le_total b c with hbc | hcb
  · exact two_cauchy_kernels_no_valley_ordered p q r b c u v hp hpq hqr hb hbc
  · simpa only [add_comm] using
      two_cauchy_kernels_no_valley_ordered p q r c b v u hp hpq hqr hc hcb

theorem four_cauchy_codebook_no_repeated_valley
    (p q r : ℝ) (b a : Fin 4 → ℝ)
    (hp : 0 < p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hb : ∀ i, 0 < b i) :
    let K := fun i s => a i * b i / (s+b i)^2
    let F₁ := fun s => -K 0 s + K 1 s - K 2 s + K 3 s
    let F₂ := fun s => -K 0 s - K 1 s + K 2 s + K 3 s
    ¬ (0 < F₁ p ∧ 0 < F₂ p ∧ F₁ q < 0 ∧ F₂ q < 0 ∧
       0 < F₁ r ∧ 0 < F₂ r) := by
  dsimp only
  intro h
  apply two_cauchy_kernels_no_valley p q r (b 3) (b 0)
    (a 3*b 3) (-a 0*b 0) hp hpq hqr (hb 3) (hb 0)
  simp only [neg_mul, neg_div]
  exact ⟨by linarith [h.1, h.2.1],
    by linarith [h.2.2.1, h.2.2.2.1],
    by linarith [h.2.2.2.2.1, h.2.2.2.2.2]⟩

end HeadComplexity
