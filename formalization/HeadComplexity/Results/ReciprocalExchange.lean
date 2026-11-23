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

/-- A three-row cyclic exchange with the third base equal to the average
of the first two has an exact quadratic sign factor. -/
theorem reciprocal_three_cycle_identity (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    1 / (u + 1) + 1 / (v + 2) + 2 / (u + v + 6) -
      1 / (u + 2) - 1 / (v + 3) - 2 / (u + v + 2) =
    (u - v) * (u - v - 2) *
      (u ^ 2 + 4 * u * v + v ^ 2 + 13 * u + 11 * v + 22) /
      ((u + 1) * (u + 2) * (v + 2) * (v + 3) *
        (u + v + 2) * (u + v + 6)) := by
  have h1 : u + 1 ≠ 0 := by positivity
  have h2 : u + 2 ≠ 0 := by positivity
  have h3 : v + 2 ≠ 0 := by positivity
  have h4 : v + 3 ≠ 0 := by positivity
  have h5 : u + v + 2 ≠ 0 := by positivity
  have h6 : u + v + 6 ≠ 0 := by positivity
  field_simp
  ring

/-- The positive factor in the three-cycle identity can be discarded
when testing its strict sign. -/
theorem reciprocal_three_cycle_pos_iff (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) :
    0 < 1 / (u + 1) + 1 / (v + 2) + 2 / (u + v + 6) -
      1 / (u + 2) - 1 / (v + 3) - 2 / (u + v + 2) ↔
      0 < (u - v) * (u - v - 2) := by
  rw [reciprocal_three_cycle_identity u v hu hv]
  have hd : 0 < (u + 1) * (u + 2) * (v + 2) * (v + 3) *
      (u + v + 2) * (u + v + 6) := by positivity
  have hp : 0 < u ^ 2 + 4 * u * v + v ^ 2 + 13 * u + 11 * v + 22 := by
    positivity
  rw [div_pos_iff_of_pos_right hd, mul_pos_iff_of_pos_right hp]

/-- An explicit admissible three-head update is zero on the inactive face
and gives a strict checkerboard correction on the active face.
This is a local update, not a universal bound on the number of heads. -/
theorem reciprocal_three_cycle_checkerboard (x y z : ℝ)
    (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) :
    let d := 1 / (2 + 3 * x + y + z) + 1 / (1 + x + 3 * y + 2 * z) +
      2 / (3 + 4 * x + 4 * y + 6 * z) - 1 / (2 + 3 * x + y + 2 * z) -
      1 / (1 + x + 3 * y + 3 * z) - 2 / (3 + 4 * x + 4 * y + 2 * z)
    (z = 0 → d = 0) ∧ (1 - 2 * x) * (1 - 2 * y) * d ≤ -z / 2100 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    rcases hz with rfl | rfl <;> norm_num

end HeadComplexity
