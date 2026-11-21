import HeadComplexity.Results.ParityHingeNonattainment

set_option linter.style.header false

/-!
A denominator-only quadratic penalty can give an attained, positive hinge
minimum in the interior of the admissible slope domain. Three margins at the
minimum are hinge kinks. This audits a proposed optimization repair, not the
universal head-complexity conjecture.
-/

namespace HeadComplexity

theorem squareParityHinge_mul_denominator_lower
    (a₀ a₁ a₂ a₃ p q : ℝ) (ha : a₀ + a₃ = a₁ + a₂)
    (hp : 0 < p) (hq : 0 < q) :
    4 + 2 * (p + q) ≤ (1 + p + q) *
      squareParityHinge a₀ a₁ a₂ a₃ 1 (1+p) (1+q) (1+p+q) := by
  have e₀ := sub_le_mul_hinge 1 a₀ (by norm_num)
  have e₁ := sub_le_mul_hinge (1+p) (-a₁) (by positivity)
  have e₂ := sub_le_mul_hinge (1+q) (-a₂) (by positivity)
  have e₃ := sub_le_mul_hinge (1+p+q) a₃ (by positivity)
  simp only [neg_div, sub_neg_eq_add] at e₁ e₂
  have u₀ := mul_le_mul_of_nonneg_right
    (show (1 : ℝ) ≤ 1+p+q by linarith) (le_max_left 0 (1-a₀/1))
  have u₁ := mul_le_mul_of_nonneg_right
    (show 1+p ≤ 1+p+q by linarith) (le_max_left 0 (1+a₁/(1+p)))
  have u₂ := mul_le_mul_of_nonneg_right
    (show 1+q ≤ 1+p+q by linarith) (le_max_left 0 (1+a₂/(1+q)))
  unfold squareParityHinge
  nlinarith

theorem regularized_squareParityHinge_ge_thirteen_quarters
    (a₀ a₁ a₂ a₃ p q : ℝ) (ha : a₀ + a₃ = a₁ + a₂)
    (hp : 0 < p) (hq : 0 < q) :
    (13 : ℝ)/4 ≤
      squareParityHinge a₀ a₁ a₂ a₃ 1 (1+p) (1+q) (1+p+q)
        + (p^2+q^2)/2 := by
  let L := squareParityHinge a₀ a₁ a₂ a₃ 1 (1+p) (1+q) (1+p+q)
  have hL : 4+2*(p+q) ≤ (1+p+q)*L :=
    squareParityHinge_mul_denominator_lower a₀ a₁ a₂ a₃ p q ha hp hq
  have h₁ : 0 ≤ (p+q-1)^2 * (p+q+3) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have h₂ : 0 ≤ (p-q)^2 * (1+p+q) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have heq : 4*(1+p+q)*(L+(p^2+q^2)/2-13/4) =
      4*((1+p+q)*L-4-2*(p+q)) +
        (p+q-1)^2*(p+q+3)+(p-q)^2*(1+p+q) := by ring
  have hprod : 0 ≤ 4*(1+p+q)*(L+(p^2+q^2)/2-13/4) := by
    rw [heq]
    linarith
  have hnonneg : 0 ≤ L+(p^2+q^2)/2-13/4 :=
    (mul_nonneg_iff_of_pos_left (show (0 : ℝ) < 4*(1+p+q) by positivity)).mp hprod
  change (13 : ℝ)/4 ≤ L+(p^2+q^2)/2
  linarith

theorem regularized_squareParityHinge_attained :
    squareParityHinge 1 (-3/2) (-3/2) (-4) 1 (3/2) (3/2) 2
      + (((1 : ℝ)/2)^2+((1 : ℝ)/2)^2)/2 = 13/4 := by
  norm_num [squareParityHinge]

end HeadComplexity
