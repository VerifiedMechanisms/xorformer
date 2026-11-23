import Mathlib.Tactic

set_option linter.style.header false

namespace HeadComplexity

/-- Exact exchange of two positive reciprocal denominators. This is an
algebraic identity, not a universal construction of Boolean scores. -/
theorem reciprocal_exchange_identity (u v a b : ℝ)
    (hua : u + a ≠ 0) (hub : u + b ≠ 0)
    (hva : v + a ≠ 0) (hvb : v + b ≠ 0) :
    1 / (u + a) + 1 / (v + b) - 1 / (u + b) - 1 / (v + a) =
      (a - b) * (u - v) * (u + v + a + b) /
        ((u + a) * (u + b) * (v + a) * (v + b)) := by
  field_simp
  ring

/-- For positive denominator values, a two-row exchange with equal
constant numerators has the sign of a single affine difference. -/
theorem reciprocal_exchange_pos_iff (u v a b : ℝ)
    (hua : 0 < u + a) (hub : 0 < u + b)
    (hva : 0 < v + a) (hvb : 0 < v + b) :
    0 < 1 / (u + a) + 1 / (v + b) - 1 / (u + b) - 1 / (v + a) ↔
      0 < (a - b) * (u - v) := by
  rw [reciprocal_exchange_identity u v a b
    (ne_of_gt hua) (ne_of_gt hub) (ne_of_gt hva) (ne_of_gt hvb)]
  have hd : 0 < (u + a) * (u + b) * (v + a) * (v + b) := by positivity
  have hs : 0 < u + v + a + b := by linarith
  rw [div_pos_iff_of_pos_right hd, mul_pos_iff_of_pos_right hs]

/-- The exact exchange formula when fixed numerators may differ. -/
theorem affine_numerator_exchange_identity (u v a b A C : ℝ)
    (hua : u + a ≠ 0) (hub : u + b ≠ 0)
    (hva : v + a ≠ 0) (hvb : v + b ≠ 0) :
    A / (u + a) + C / (v + b) - A / (u + b) - C / (v + a) =
      (b - a) * (A * (v + a) * (v + b) - C * (u + a) * (u + b)) /
        ((u + a) * (u + b) * (v + a) * (v + b)) := by
  field_simp
  ring

end HeadComplexity
