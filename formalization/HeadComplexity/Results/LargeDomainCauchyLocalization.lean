import HeadComplexity.Results.LargeDomainWeightedTangent

set_option linter.style.header false

namespace HeadComplexity.LargeDomain

/-- Positive Cauchy profiles with ordered poles have only this much relative
variation, regardless of the range of nonnegative row addresses. -/
theorem cauchy_ratio_bounds {b₁ b₂ t : ℝ} (hb₁ : 0 < b₁)
    (hb : b₁ ≤ b₂) (ht : 0 ≤ t) :
    1 ≤ (b₂ + t) / (b₁ + t) ∧ (b₂ + t) / (b₁ + t) ≤ b₂ / b₁ := by
  have hd : 0 < b₁ + t := by positivity
  constructor
  · exact (le_div_iff₀ hd).2 (by linarith)
  · apply (div_le_div_iff₀ hd hb₁).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) ht]

/-- Raising a compact positive Cauchy profile to a power cannot provide large
relative localization unless the exponent times pole width is large. -/
theorem cauchy_power_ratio_bounds {b₁ b₂ t : ℝ} (hb₁ : 0 < b₁)
    (hb : b₁ ≤ b₂) (ht : 0 ≤ t) (p : ℕ) :
    1 ≤ ((b₂ + t) / (b₁ + t)) ^ p ∧
      ((b₂ + t) / (b₁ + t)) ^ p ≤ (b₂ / b₁) ^ p := by
  obtain ⟨hl, hu⟩ := cauchy_ratio_bounds hb₁ hb ht
  constructor
  · exact one_le_pow₀ hl
  · exact pow_le_pow_left₀ (by positivity) hu p

/-- Two positive amplitude profiles cannot robustly select two different
sources beyond the explicit pole-ratio bound. The hypotheses are precisely
the two opposite dominance requirements after canceling positive factors. -/
theorem opposite_cauchy_dominance_le {b₁ b₂ t₁ t₂ α R : ℝ}
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hα : 0 < α) (hR : 0 ≤ R) (p : ℕ)
    (hfirst : R ≤ α * ((b₂ + t₁) / (b₁ + t₁)) ^ p)
    (hsecond : R * α * ((b₂ + t₂) / (b₁ + t₂)) ^ p ≤ 1) :
    R ^ 2 ≤ (b₂ / b₁) ^ p := by
  obtain ⟨_, hu⟩ := cauchy_power_ratio_bounds hb₁ hb ht₁ p
  obtain ⟨hl, _⟩ := cauchy_power_ratio_bounds hb₁ hb ht₂ p
  have hRa : 0 ≤ R * α := mul_nonneg hR hα.le
  have hsecond' : R * α ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hl hRa
    nlinarith
  have hfirst' : R ≤ α * (b₂ / b₁) ^ p :=
    hfirst.trans (mul_le_mul_of_nonneg_left hu hα.le)
  have hb₂pos : 0 < b₂ := hb₁.trans_le hb
  have hpow : 0 ≤ (b₂ / b₁) ^ p := by positivity
  have hmul := mul_le_mul_of_nonneg_left hfirst' hR
  have hbound := mul_le_mul_of_nonneg_right hsecond' hpow
  nlinarith

/-- In the compact interval `(1,1+η)`, the obstruction is at most `(1+η)^p`.
No lower bound for signed cancellation or the whole model is claimed. -/
theorem opposite_compact_cauchy_dominance_le {b₁ b₂ t₁ t₂ α R η : ℝ}
    (hb₁ : 1 < b₁) (hb : b₁ ≤ b₂) (hb₂ : b₂ < 1 + η)
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hα : 0 < α) (hR : 0 ≤ R) (p : ℕ)
    (hfirst : R ≤ α * ((b₂ + t₁) / (b₁ + t₁)) ^ p)
    (hsecond : R * α * ((b₂ + t₂) / (b₁ + t₂)) ^ p ≤ 1) :
    R ^ 2 ≤ (1 + η) ^ p := by
  have hb₁pos : 0 < b₁ := by linarith
  have hb₂pos : 0 < b₂ := hb₁pos.trans_le hb
  have hη : 0 < η := by linarith
  have hratio : b₂ / b₁ ≤ 1 + η := by
    apply (div_le_iff₀ hb₁pos).2
    nlinarith
  exact (opposite_cauchy_dominance_le hb₁pos hb ht₁ ht₂ hα hR p hfirst hsecond).trans
    (pow_le_pow_left₀ (by positivity) hratio p)

end HeadComplexity.LargeDomain
