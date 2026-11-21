import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- Two fractions whose cancellation has a stable confluent limit.
Admissibility of affine coefficients is supplied separately. -/
noncomputable def confluentPairScore (C U V B epsilon : ℝ) : ℝ :=
  (C + U / epsilon) / B - (U / epsilon) / (B + epsilon * V)

/-- The exact error from a finite two-fraction lift of a rank-one
quadratic numerator over a squared denominator. -/
theorem confluentPairScore_error_identity (C U V B epsilon : ℝ)
    (hB : B ≠ 0) (hepsilon : epsilon ≠ 0)
    (hnew : B + epsilon * V ≠ 0) :
    confluentPairScore C U V B epsilon - (C / B + U * V / B ^ 2) =
      -epsilon * U * V ^ 2 / (B ^ 2 * (B + epsilon * V)) := by
  dsimp [confluentPairScore]
  field_simp
  ring

/-- A pointwise explicit estimate, to be summed over heads and made
smaller than a strict margin. It is not an existence theorem for the
confluent representation itself. -/
theorem confluentPairScore_error_le (C U V B epsilon : ℝ)
    (hB : 0 < B) (hepsilon : epsilon ≠ 0)
    (hsmall : |epsilon * V| ≤ B / 2) :
    |confluentPairScore C U V B epsilon - (C / B + U * V / B ^ 2)| ≤
      2 * |epsilon| * |U| * |V| ^ 2 / B ^ 3 := by
  have hhalf : B / 2 ≤ B + epsilon * V := by
    have h := (abs_le.mp hsmall).1
    linarith
  have hnew : 0 < B + epsilon * V := lt_of_lt_of_le (by positivity) hhalf
  rw [confluentPairScore_error_identity C U V B epsilon hB.ne' hepsilon hnew.ne']
  simp only [abs_div, abs_mul, abs_neg, abs_pow, abs_of_pos hB, abs_of_pos hnew]
  calc
    |epsilon| * |U| * |V| ^ 2 / (B ^ 2 * (B + epsilon * V)) ≤
        |epsilon| * |U| * |V| ^ 2 / (B ^ 2 * (B / 2)) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hhalf (sq_nonneg B))
    _ = 2 * |epsilon| * |U| * |V| ^ 2 / B ^ 3 := by
      field_simp

end HeadComplexity
