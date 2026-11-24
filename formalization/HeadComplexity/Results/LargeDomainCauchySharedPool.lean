import HeadComplexity.Results.LargeDomainCauchyLocalization

set_option linter.style.header false

namespace HeadComplexity.LargeDomain

/-- The numerator governing a two-pattern shared-amplitude obstruction. -/
def sharedPoolPolynomial (q : ℝ) : ℝ :=
  2 * q ^ 10 - 40 * q ^ 9 + 339 * q ^ 8 - 1584 * q ^ 7 +
    4432 * q ^ 6 - 7488 * q ^ 5 + 7135 * q ^ 4 - 2808 * q ^ 3 -
    756 * q ^ 2 + 912 * q - 136

lemma sharedPoolPolynomial_pos {q : ℝ} (hq : 10 ≤ q) :
    0 < sharedPoolPolynomial q := by
  have hr : 0 ≤ q - 10 := by linarith
  have heq : sharedPoolPolynomial q =
      2 * (q - 10) ^ 10 + 160 * (q - 10) ^ 9 + 5739 * (q - 10) ^ 8 +
      121536 * (q - 10) ^ 7 + 1682752 * (q - 10) ^ 6 +
      15916032 * (q - 10) ^ 5 + 104140735 * (q - 10) ^ 4 +
      465434592 * (q - 10) ^ 3 + 1359716004 * (q - 10) ^ 2 +
      2344483392 * (q - 10) + 1811675384 := by
    unfold sharedPoolPolynomial
    ring
  rw [heq]
  positivity

/-- This scalar combination of minors is negative for every exterior width
`q ≥ 10`. Its sign is stable as the three poles coalesce. -/
lemma sharedPool_cauchy_minor_neg {q : ℝ} (hq : 10 ≤ q) :
    (1 / q ^ 2) *
        ((1 / (q - 2) ^ 2) * (1 / (q - 4) ^ 2) - (1 / (q - 3) ^ 2) ^ 2) -
      (1 / (q - 1) ^ 2) ^ 2 * (1 / (q - 4) ^ 2) +
      (1 / (q - 2) ^ 2) ^ 3 < 0 := by
  have h0 : q ≠ 0 := by linarith
  have h1 : q - 1 ≠ 0 := by linarith
  have h2 : q - 2 ≠ 0 := by linarith
  have h3 : q - 3 ≠ 0 := by linarith
  have h4 : q - 4 ≠ 0 := by linarith
  have hid : (1 / q ^ 2) *
        ((1 / (q - 2) ^ 2) * (1 / (q - 4) ^ 2) - (1 / (q - 3) ^ 2) ^ 2) -
      (1 / (q - 1) ^ 2) ^ 2 * (1 / (q - 4) ^ 2) +
      (1 / (q - 2) ^ 2) ^ 3 =
      -2 * sharedPoolPolynomial q /
        (q ^ 2 * (q - 4) ^ 2 * (q - 3) ^ 4 * (q - 2) ^ 6 * (q - 1) ^ 4) := by
    unfold sharedPoolPolynomial
    field_simp
    ring
  rw [hid]
  have hp := sharedPoolPolynomial_pos hq
  have hd : 0 < q ^ 2 * (q - 4) ^ 2 * (q - 3) ^ 4 *
      (q - 2) ^ 6 * (q - 1) ^ 4 := by positivity
  exact div_neg_of_neg_of_pos (by nlinarith) hd

/-- Two one-level Cauchy sign problems can each admit positive amplitudes
without admitting a common positive amplitude pool. The three displayed
inequalities are selected rows of the sign patterns `(-,+,+)` and `(+,-,+)`
for the matrix `K i j = 1 / (q-i-j)^2`, with indices zero through two.
Only positivity of the first amplitude is needed for the contradiction. -/
theorem no_shared_positive_cauchy_pool {q z₀ z₁ z₂ : ℝ}
    (hq : 10 ≤ q) (hz₀ : 0 < z₀)
    (hfirst : 0 < z₀ / q ^ 2 - z₁ / (q - 1) ^ 2 - z₂ / (q - 2) ^ 2)
    (hsecond : 0 < -z₀ / (q - 1) ^ 2 + z₁ / (q - 2) ^ 2 - z₂ / (q - 3) ^ 2)
    (hthird : 0 < z₀ / (q - 2) ^ 2 - z₁ / (q - 3) ^ 2 + z₂ / (q - 4) ^ 2) :
    False := by
  let a : ℝ := 1 / q ^ 2
  let b : ℝ := 1 / (q - 1) ^ 2
  let c : ℝ := 1 / (q - 2) ^ 2
  let e : ℝ := 1 / (q - 3) ^ 2
  let f : ℝ := 1 / (q - 4) ^ 2
  have h1 : q - 1 ≠ 0 := by linarith
  have h2 : q - 2 ≠ 0 := by linarith
  have h3 : q - 3 ≠ 0 := by linarith
  have h4 : q - 4 ≠ 0 := by linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hf : 0 < f := by dsimp [f]; positivity
  have hΔ : 0 < c * f - e ^ 2 := by
    have hid : c * f - e ^ 2 =
        (2 * q ^ 2 - 12 * q + 17) /
          ((q - 4) ^ 2 * (q - 3) ^ 4 * (q - 2) ^ 2) := by
      dsimp [c, e, f]
      field_simp
      ring
    rw [hid]
    apply div_pos
    · nlinarith [sq_nonneg (q - 10)]
    · positivity
  have hminor : a * (c * f - e ^ 2) - b ^ 2 * f + c ^ 3 < 0 :=
    sharedPool_cauchy_minor_neg hq
  have hfirst' : 0 < a * z₀ - b * z₁ - c * z₂ := by
    simpa [a, b, c, div_eq_mul_inv, mul_comm] using hfirst
  have hsecond' : 0 < -b * z₀ + c * z₁ - e * z₂ := by
    simpa [b, c, e, div_eq_mul_inv, mul_comm] using hsecond
  have hthird' : 0 < c * z₀ - e * z₁ + f * z₂ := by
    simpa [c, e, f, div_eq_mul_inv, mul_comm] using hthird
  have hsum : 0 <
      (c * f - e ^ 2) * (a * z₀ - b * z₁ - c * z₂) +
      (b * f + c * e) * (-b * z₀ + c * z₁ - e * z₂) +
      (c ^ 2 + b * e) * (c * z₀ - e * z₁ + f * z₂) := by
    positivity
  have hid :
      (c * f - e ^ 2) * (a * z₀ - b * z₁ - c * z₂) +
      (b * f + c * e) * (-b * z₀ + c * z₁ - e * z₂) +
      (c ^ 2 + b * e) * (c * z₀ - e * z₁ + f * z₂) =
      (a * (c * f - e ^ 2) - b ^ 2 * f + c ^ 3) * z₀ := by ring
  rw [hid] at hsum
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hminor.le hz₀.le)) hsum

/-- The leading two-by-two principal minor of the exterior square-Cauchy
matrix is strictly positive. -/
lemma sharedPool_principal_minor_pos {q : ℝ} (hq : 10 ≤ q) :
    0 < (1 / q ^ 2) * (1 / (q - 2) ^ 2) - (1 / (q - 1) ^ 2) ^ 2 := by
  have h0 : q ≠ 0 := by linarith
  have h1 : q - 1 ≠ 0 := by linarith
  have h2 : q - 2 ≠ 0 := by linarith
  have hid : (1 / q ^ 2) * (1 / (q - 2) ^ 2) - (1 / (q - 1) ^ 2) ^ 2 =
      (2 * q ^ 2 - 4 * q + 1) / (q ^ 2 * (q - 1) ^ 4 * (q - 2) ^ 2) := by
    field_simp
    ring
  rw [hid]
  apply div_pos
  · nlinarith [sq_nonneg (q - 10)]
  · positivity

/-- No unrestricted real amplitude vector can solve both Cauchy sign systems
`(-,+,+)` and `(+,-,+)`. Five of their six rows already give a contradiction;
positivity of an amplitude is a consequence, not an assumption. -/
theorem no_shared_cauchy_pool {q z₀ z₁ z₂ : ℝ} (hq : 10 ≤ q)
    (hσ₀ : 0 < z₀ / q ^ 2 - z₁ / (q - 1) ^ 2 - z₂ / (q - 2) ^ 2)
    (hσ₁ : 0 < -z₀ / (q - 1) ^ 2 + z₁ / (q - 2) ^ 2 + z₂ / (q - 3) ^ 2)
    (hτ₀ : 0 < z₀ / q ^ 2 - z₁ / (q - 1) ^ 2 + z₂ / (q - 2) ^ 2)
    (hτ₁ : 0 < -z₀ / (q - 1) ^ 2 + z₁ / (q - 2) ^ 2 - z₂ / (q - 3) ^ 2)
    (hτ₂ : 0 < z₀ / (q - 2) ^ 2 - z₁ / (q - 3) ^ 2 + z₂ / (q - 4) ^ 2) :
    False := by
  let a : ℝ := 1 / q ^ 2
  let b : ℝ := 1 / (q - 1) ^ 2
  let c : ℝ := 1 / (q - 2) ^ 2
  have h1 : q - 1 ≠ 0 := by linarith
  have h2 : q - 2 ≠ 0 := by linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hΔ : 0 < a * c - b ^ 2 := sharedPool_principal_minor_pos hq
  have hA : 0 < a * z₀ - b * z₁ := by
    have hsum : 0 < z₀ / q ^ 2 - z₁ / (q - 1) ^ 2 := by linarith
    simpa [a, b, div_eq_mul_inv, mul_comm] using hsum
  have hB : 0 < -b * z₀ + c * z₁ := by
    have hsum : 0 < -z₀ / (q - 1) ^ 2 + z₁ / (q - 2) ^ 2 := by linarith
    simpa [b, c, div_eq_mul_inv, mul_comm] using hsum
  have hprod : 0 < (a * c - b ^ 2) * z₀ := by
    calc
      0 < c * (a * z₀ - b * z₁) + b * (-b * z₀ + c * z₁) := by positivity
      _ = (a * c - b ^ 2) * z₀ := by ring
  have hz₀ : 0 < z₀ := (mul_pos_iff_of_pos_left hΔ).mp hprod
  exact no_shared_positive_cauchy_pool hq hz₀ hσ₀ hτ₁ hτ₂

end HeadComplexity.LargeDomain
